package main.lib_assembler;

import main.config.BmConfig;
import main.encode.*;
import main.eval.*;

import java.util.*;
import java.util.stream.Collectors;

import static main.eval.CompressionEval.compressLibTacs;

/*
 * This class is for assembling candidate tactics into a full tactic library.
 * Ideally, the library should be as close to optimal as possible.
 * Several sampling types are supported:
 *  - none (all subsets of tactics are tried)
 *  - greedy (tactics are immediately taken when they improve the compression rate)
 */

public class LibAssembler {
    private final static int BEAM_POOL_SIZE = 20;

    public enum AssemblyType {
        NONE,
        GREEDY,
        BEAM
    }

    public static class Library implements Comparable<Library> {
        public List<CoqProof> corpus;
        public List<Set<Integer>> corpusVertices = new ArrayList<>();
        List<Integer> trainingIndices;
        public List<CoqProof> tactics;
        public List<CoqProof> unusedTacs;

        private int corpusSize;
        private int trainingSize;
        private int testingCompressedSize;
        private int compressedSize;
        private int librarySize;
        public int numCompressedProofs = 0;
        Map<String, List<Integer>> tacticOccurrences = new HashMap<>(); // key: tactic, values: graph index(can be dup if tactic is used multiple times)

        private int corpusHashCode;

        public Library(List<CoqProof> corpus) {
            this.corpus = new ArrayList<>();
            for (CoqProof each: corpus) {
                this.corpus.add(new CoqProof(each));
                Set<Integer> uncompressedVertices = new HashSet<>();
                for (int v = 0; v < each.tactics.size(); v++) {
                    uncompressedVertices.add(v);
                }
                this.corpusVertices.add(uncompressedVertices);
            }
            this.tactics = new ArrayList<>();

            this.corpusHashCode = corpus.hashCode();

            this.corpusSize = this.compressedSize = this.librarySize = 0;
            // Populate sizes
            for (CoqProof each: corpus) {
                this.corpusSize += each.tactics.size();
                this.compressedSize += each.tactics.size();
            }

            this.unusedTacs = new ArrayList<>();
            this.numCompressedProofs = 0;
        }

        public Library(Library o) {
            this.corpus = new ArrayList<>();
            for (CoqProof each: o.corpus) {
                this.corpus.add(new CoqProof(each));
            }
            this.tactics = new ArrayList<>();
            for (CoqProof each: o.tactics) {
                this.tactics.add(new CoqProof(each));
            }
            this.corpusVertices = new ArrayList<>();
            for (Set<Integer> vs: o.corpusVertices) {
                this.corpusVertices.add(new HashSet<>(vs));
            }
            this.corpusSize = o.corpusSize;
            this.compressedSize = o.compressedSize;
            this.librarySize = o.librarySize;
            this.trainingSize = o.trainingSize;
            this.unusedTacs = new ArrayList<>();
            for (CoqProof each: o.unusedTacs) {
                this.unusedTacs.add(new CoqProof(each));
            }

            this.corpusHashCode = o.corpusHashCode;
            this.trainingIndices = o.trainingIndices;
            this.testingCompressedSize = o.testingCompressedSize;
            this.numCompressedProofs = o.numCompressedProofs;
            this.tacticOccurrences = o.tacticOccurrences;
        }

        public Library addCompressLib(CoqProof tactic) {
            List<CoqProof> compressedCorpus = new ArrayList<>();
            List<Set<Integer>> comprCorpusVertices = new ArrayList<>();

            // sort on tac size, s.t. we only have to check subgraph in one direction
            int tacSize = tactic.tactics.size(); //compressTacs ? tactic.tactics.size() : compressExtractedTactic(tactic, new ArrayList<>(this.tactics));

            // check if current tactic library can be compressed using current tactic, if yes, return the decrease in total size
            List<CoqProof> libTacs = new ArrayList<>(this.tactics);

            int candidateSize = 0;
            int candidateSizeTraining = 0;
            for (int i = 0; i < corpus.size(); i++) {
                // compress current proof with the extracted tactic
                CoqProof compressed = corpus.get(i);
                // if current tactics match current proof, check if the corresponding vertices are still uncompressed
                Set<Integer> compressedVertices = new HashSet<>(this.corpusVertices.get(i));
                if (tactic.matches.containsKey(i)) {
                    boolean compressible = true;
                    for (int v: tactic.matches.get(i)) {
                        if (!compressedVertices.contains(v)) {
                            compressible = false;
                        }
                    }

                    if (compressible) {
                       compressedVertices.removeAll(tactic.matches.get(i));
                        int compressedTac = -1;
                        while (compressedVertices.contains(compressedTac)) {
                            compressedTac--;
                        }
                        compressedVertices.add(compressedTac);
                    }
                }
                // add the compressed proof to the compressedCorpus
                compressedCorpus.add(compressed);
                comprCorpusVertices.add(compressedVertices);

                // add the size of the compressed proof
                if (this.trainingIndices.contains(i)) {
                    // if current graph is not in the training data
                    candidateSizeTraining += compressedVertices.size();
                }
                candidateSize += compressedVertices.size();
            }

            System.out.println("tacsize is: " + tacSize);
            System.out.println("adding " + tactic.raw_string + " to the prev lib:");
            for (CoqProof p: this.tactics) {
                System.out.println(p.raw_string);
            }
            System.out.println("-------------------------------------------------");



            int libSizeDecrease = 0;
            Library lib = new Library(this);
            if (candidateSize - candidateSizeTraining <= this.getTestingCompressedSize()) {
                // This tactic is beneficial, so let's keep it
                lib.corpus = compressedCorpus; // Compress corpus
                lib.corpusVertices = comprCorpusVertices;
                lib.tactics = new ArrayList<>(libTacs);
                lib.tactics.add(tactic); // Add to library

                lib.compressedSize = candidateSize; // update sizes
                lib.testingCompressedSize = candidateSize - candidateSizeTraining;
                lib.librarySize += (tacSize - libSizeDecrease);

                // change lib.unused: try compress all unused tacs with current tac, if any tacs got changed, we remove that tactic
                List<List<CoqProof>> unusedCompressed = compressLibTacs(tactic, new ArrayList<>(lib.unusedTacs));
                if (unusedCompressed.size() > 1) {
                    Set<CoqProof> remove = new HashSet<>();
                    List<CoqProof> unused = unusedCompressed.get(1);
                    // compressible
                    for (int i = 0; i < unused.size(); i++) {
                        // if current tac can be compressed
                        if (lib.unusedTacs.get(i).tactics.size() > unused.get(i).tactics.size()) {
                            remove.add(lib.unusedTacs.get(i));
                        }
                    }

                    for (CoqProof r: remove) {
                        lib.unusedTacs.remove(r);
                    }
                }
                return lib;
            }
            return null;
        }

        public List<Library> addAndCompress(CoqProof tactic) {
            List<CoqProof> compressedCorpus = new ArrayList<>();

            // check if current tactic can be compressed using any previous tactics, if yes, return the compressed size of current tactic
            // this is useless, because when if smaller tactics are already applied, the larger tactics won't be able to be useful at all
            int tacSize = tactic.tactics.size(); //compressTacs ? tactic.tactics.size() : compressExtractedTactic(tactic, new ArrayList<>(this.tactics));

            // check if current tactic library can be compressed using current tactic, if yes, return the decrease in total size
            List<List<CoqProof>> libCopies = compressLibTacs(tactic, new ArrayList<>(this.tactics));

            int candidateSize = 0;
            int candidateSizeTesting = 0;
            for (int i = 0; i < corpus.size(); i++) {
                // compress current proof with the extracted tactic
                CoqProof compressed = CompressionEval.compressProof(corpus.get(i), tactic, i);

                // add the compressed proof to the compressedCorpus
                compressedCorpus.add(compressed);

                // add the size of the compressed proof
                if (!this.trainingIndices.contains(i)) {
                    // if current graph is not in the training data
                    candidateSizeTesting += compressed.tactics.size();
                }
                candidateSize += compressed.tactics.size();
            }

            System.out.println("tacsize is: " + tacSize);
            System.out.println("adding " + tactic.raw_string + " to the prev lib:");
            for (CoqProof p: this.tactics) {
                System.out.println(p.raw_string);
            }


            List<Library> res = new ArrayList<>();
            for (List<CoqProof> libCopy : libCopies) {
                int libSizeDecrease = 0;
                Library lib = new Library(this);
                if (libCopies.indexOf(libCopy) == 1) {
                    for (int i = 0; i < libCopy.size(); i++) {
                        libSizeDecrease += (this.tactics.get(i).tactics.size() - libCopy.get(i).tactics.size());
                    }
                }
                if (candidateSize + tacSize - libSizeDecrease < this.getCompressedSize()) {
                    // This tactic is beneficial, so let's keep it
                    lib.corpus = compressedCorpus; // Compress corpus
                    lib.tactics = new ArrayList<>(libCopy);
                    lib.tactics.add(tactic); // Add to library

                    lib.compressedSize = candidateSize; // update sizes
                    lib.librarySize += (tacSize - libSizeDecrease);
                    res.add(lib);
                }
            }
            return res;
        }

        public int getCorpusSize() {
            return corpusSize;
        }
        
        public int getTrainingSize() { return trainingSize; }

        public void setTrainingIndices(List<Integer> trainingIndices) {
            int size = 0;
            this.trainingIndices = trainingIndices;
            for (int i: trainingIndices) {
                size += this.corpus.get(i).tactics.size();
            }
            this.trainingSize = size;
            int testingSize = 0;
            for (int i = 0; i < this.corpus.size(); i++) {
                if (!trainingIndices.contains(i)) {
                     testingSize += this.corpus.get(i).tactics.size();
                }
            }
            this.testingCompressedSize = testingSize;
        }

        public int getCompressedSize() {
            return compressedSize;
        }

        public int getTestingCompressedSize() {
            return this.testingCompressedSize;
        }

        public int getLibrarySize() {
            return librarySize;
        }

        public int getOverallSize() {
            return compressedSize + librarySize;
        }

        public double getCompression() {
            return (double) corpusSize / (compressedSize + librarySize);
        }

        @Override
        public int compareTo(Library o) {
            if (this.getCorpusSize() != o.getCorpusSize()) {
                System.err.println("Different proof corpuses: libraries not comparable");
                return 0;
            }
            return Integer.compare(this.getOverallSize(), o.getOverallSize());
        }

        @Override
        public boolean equals(Object o){
            if(! (o instanceof Library)) return false;

            Library lib = (Library) o;
            return this.corpus.equals(lib.corpus) && this.tactics.equals(lib.tactics);
        }

        @Override
        public int hashCode() {
            return this.corpusHashCode + this.tactics.hashCode(); // avoid re-hashing the entire corpus
        }

        public String printTactics() {
            Set<String> tacticRawString = new HashSet<>();
            StringBuilder sb = new StringBuilder();
            for (CoqProof tac: this.tactics) {
                if (tacticRawString.contains(tac.raw_string.split(" := ")[1])) {
                    continue;
                }
                tacticRawString.add(tac.raw_string.split(" := ")[1]);
                sb.append("Ltac ").append(tac.raw_string)
                        .append("\n");
            }
            return sb.toString();
        }

        public String printCompressionRate() {
            StringBuilder sb = new StringBuilder("compression_rate\n");
            int testingSize = this.getCorpusSize() - this.trainingSize;

            // original_size, compressed_size, compression_rate
            sb.append(String.format("%.2f", (double) (testingSize) / this.testingCompressedSize))
              .append("\n");

            return sb.toString();
        }

        public String printTacticsStats() {
            StringBuilder sb = new StringBuilder("tactics_learned,avg_tactic_size,max_tactic_size,tactic_usage_count\n");
            int minusSize = 0;
            Set<String> tacticRawString = new HashSet<>();
            for (CoqProof tac: this.tactics) {
                if (tacticRawString.contains(tac.raw_string.split(" := ")[1])) {
                    minusSize += tac.tactics.size();
                    continue;
                }
                tacticRawString.add(tac.raw_string.split(" := ")[1]);
            }
            int maxTacSize = 0;
            for (CoqProof t: this.tactics) {
                if (t.tactics.size() > 50) {
                    tacticRawString.remove(t.raw_string.split(" := ")[1]);
                    minusSize += t.tactics.size();
                    continue;
                }
                if (t.tactics.size() > maxTacSize) {
                    maxTacSize = t.tactics.size();
                }
            }
            int numTotalApplications = this.tacticOccurrences.values().stream().map(l -> l.size()).toList()
                    .stream().reduce(0, Integer::sum);
            sb.append(tacticRawString.size()).append(",")
              .append(String.format("%.2f", (double) (this.getLibrarySize() - minusSize) / tacticRawString.size())).append(",")
              .append(maxTacSize).append(",")
              .append(numTotalApplications).append("\n");
            return sb.toString();
        }

        @Override
        public String toString() {
            StringBuilder ret = new StringBuilder("Corpus: ");
            for (CoqProof each: this.corpus) {
                ret.append("\n" + each.condensedToString());
            }
            ret.append("\nTactics: ");
            for (CoqProof each: this.tactics) {
                ret.append("\n" + each.condensedToString());
            }
            return ret.append("\n").toString();
        }
    }


    public static Library assembleLibraryForEnumerateGreedy(List<CoqProof> corpus, List<CoqProof> compressedCorpus, Collection<CoqProof> customTacs,
                                                            AssemblyType type, List<Integer> trainingIndices) {
        Library lib = new Library(corpus);
        lib.setTrainingIndices(trainingIndices);
        for (CoqProof t: customTacs) {
            lib.tactics.add(t);
            lib.librarySize += t.tactics.size();
        }
        lib.numCompressedProofs = 0;
        lib.compressedSize = 0;
        lib.testingCompressedSize = 0;
        lib.tacticOccurrences = new HashMap<>();
        for (int i = 0; i < corpus.size(); i++) {
            for (CoqTactic tactic: compressedCorpus.get(i).tactics) {
                if (tactic.sig_no_out_arg.contains("custom")) {
                    if (tactic.sig_no_out_arg.contains("custom0 _i _o _o _o _o _o _o _o _o _o _o _o _o _o _o _o _o _o _o _o _o _o _i _i _i _i _o _i _i _i _i _i _i _i _i _o _i _i _i _i _i _i _i _o _i _i _o _i _i _i _i _o _i _i _i _i _i _i _i _i _i _o _i _i _i _i _i _o _i _i _i _i _i _i _o _i _i")) {
                        if (trainingIndices.size() == lib.corpus.size() || !trainingIndices.contains(i)) {
                            lib.testingCompressedSize += (lib.tactics.get(0).tactics.size() - 1);
                        }
                        continue;
                    }
                    if (!lib.tacticOccurrences.containsKey(tactic.sig_no_out_arg)) {
                        lib.tacticOccurrences.put(tactic.sig_no_out_arg, new ArrayList<>());
                    }
                    lib.tacticOccurrences.get(tactic.sig_no_out_arg).add(i);
                }
            }
            lib.compressedSize += compressedCorpus.get(i).tactics.size();
            if (trainingIndices.size() == lib.corpus.size() || !trainingIndices.contains(i)) {
                if (corpus.get(i).tactics.size() > compressedCorpus.get(i).tactics.size()) {
                    lib.numCompressedProofs++;
                }
                lib.testingCompressedSize += compressedCorpus.get(i).tactics.size();
            }
        }
        return lib;
    }

    public static Library assembleLibraryForEnumerate(List<CoqProof> corpus, Collection<CoqProof> customTacs,
                                                      AssemblyType type, List<Integer> trainingIndices) {
        switch (type) {
            case GREEDY: {
                Library lib = new Library(corpus);
                lib.setTrainingIndices(trainingIndices);
                Map<Integer, List<Integer>> mappedVertices = new HashMap<>(); // mapped vertices is

                // candidates already sorted on its utility
                for (CoqProof t: customTacs) {
                    boolean skip = false;
                    for (Integer g: t.matches.keySet()) {
                        for (int v: t.matches.get(g)) {
                            if (mappedVertices.containsKey(g) && mappedVertices.get(g).contains(v)) {
                                // if overlapped
                                skip = true;
                                break;
                            }
                        }
                        if (skip) break;
                    }
                    if (skip) continue;

                    // if add current tactics, add all mapped vertices to the map
                    int compressedSize = 0;
                    int testingCompressedSize = 0;
                    for (Integer g: t.matches.keySet()) {
                        if (!mappedVertices.containsKey(g))
                            mappedVertices.put(g, new ArrayList<>());
                        mappedVertices.get(g).addAll(t.matches.get(g));
                        compressedSize += t.matches.get(g).size();
                        if (!trainingIndices.contains(g)) {
                            testingCompressedSize += t.matches.get(g).size();
                        }
                    }


                    // update utility stuff
                    lib.tactics.add(t);
                    lib.compressedSize -= (compressedSize - compressedSize / t.tactics.size());
                    lib.testingCompressedSize -= (testingCompressedSize - testingCompressedSize / t.tactics.size());
                    lib.librarySize += t.tactics.size();
                }
                return lib;
            } case NONE: {
                // exhaustive
                customTacs = customTacs.stream().sorted((t1, t2) -> t1.tactics.size() - t2.tactics.size()).collect(Collectors.toList());
                PriorityQueue<Library> currPool = new PriorityQueue<>();

                Library currLib = new Library(corpus);
                currLib.setTrainingIndices(trainingIndices);
                currLib.tactics = new ArrayList<>();
                currLib.unusedTacs = new ArrayList<>(customTacs);
                currPool.add(currLib);
                Library bestLib = currLib;
                int bestCompressedSize = currLib.getTestingCompressedSize();

                while (!currPool.isEmpty()) {
                    currLib = currPool.peek();
                    if (currLib.unusedTacs.isEmpty()) {
                        currPool.poll();
                        if (currLib.getTestingCompressedSize() < bestCompressedSize) {
                            bestLib = currLib;
                            bestCompressedSize = bestLib.getTestingCompressedSize();
                        }
                        continue;
                    }
                    CoqProof currTactic = currLib.unusedTacs.remove(0);
                    Library newLib = new Library(currLib);
                    newLib = newLib.addCompressLib(currTactic);
                    if (newLib != null) {
                        System.out.println("adding new lib");
                        currPool.add(newLib);
                    }
                }
                return bestLib;
            } default: {
                System.err.println("Sampling Type not yet supported");
                return new Library(corpus);
            }
        }
    }

    public static Library assembleLibrary(List<CoqProof> corpus, Collection<CoqProof> customTacs, AssemblyType type) {
        customTacs = customTacs.stream().sorted((t1, t2) -> Integer.compare(t2.tactics.size(), t1.tactics.size())).collect(Collectors.toList());
        // filter duplicate and empty customTac
        switch(type) {
            case NONE: {
                PriorityQueue<Library> currPool = new PriorityQueue<>();

                Library currLib = new Library(corpus);
                currLib.tactics = new ArrayList<>();
                currLib.unusedTacs = new ArrayList<>(customTacs);
                currPool.add(currLib);
                Library bestLib = currLib;
                int bestCompressedSize = currLib.getOverallSize();

                while (!currPool.isEmpty()) {
                    currLib = currPool.peek();
                    if (currLib.unusedTacs.isEmpty()) {
                        currPool.poll();
                        if (currLib.getOverallSize() < bestCompressedSize) {
                            bestLib = currLib;
                            bestCompressedSize = bestLib.getOverallSize();
                        }
                        continue;
                    }
                    CoqProof currTactic = currLib.unusedTacs.remove(0);
                    Library newLib = new Library(currLib);
                    List<Library> newLibs = newLib.addAndCompress(currTactic);
                    if (!newLibs.isEmpty()) {
                        System.out.println("adding new libs");
                        currPool.addAll(newLibs);
                    }
                }
                return bestLib;
            }
            case GREEDY: {
                Library currLib = new Library(corpus);
                Library bestLib = currLib;
                int bestCompressedSize = currLib.getOverallSize();

                currLib.tactics = new ArrayList<>();
                currLib.unusedTacs = new ArrayList<>(customTacs);
                Queue<Library> currPool = new PriorityQueue<>();
                currPool.add(currLib);
                while (!currPool.isEmpty()) {
                    currLib = currPool.peek();
                    if (currLib.unusedTacs.isEmpty()) {
                        currLib = currPool.poll();
                        if (currLib.getOverallSize() < bestCompressedSize) {
                            bestLib = currLib;
                            bestCompressedSize = bestLib.getOverallSize();
                        }
                        continue;
                    }
                    CoqProof currTactic = currLib.unusedTacs.remove(0);
                    Library newLib = new Library(currLib);
                    List<Library> newLibs = newLib.addAndCompress(currTactic);
                    if (!newLibs.isEmpty()) {
                        System.out.println("adding new libs");
                        currPool.poll();
                        currPool.addAll(newLibs);
                    }
                }
                return bestLib;
            }
            case BEAM: {
                // create a library of the current input proof corpus
                Library bestLibrary = new Library(corpus);

                Set<Library> currentPool = new HashSet<>();
                currentPool.add(new Library(bestLibrary));

                // for each extracted tactic
                System.out.println("customtac has size " + customTacs.size());
                for (int size = 1; size <= customTacs.size(); size++) {
                    PriorityQueue<Library> nextPool = new PriorityQueue<>();
                    // for each library in the current pool, which is the current compressed lib
                    for (Library lib : currentPool) {
                        for (CoqProof custom : customTacs) {
                            // create a copy of current pooled library
                            Library copy = new Library(lib);
                            if (lib.tactics.contains(custom)) continue;
                            List<Library> newLibs = copy.addAndCompress(custom);
                            if (!newLibs.isEmpty()) { // We'll only consider tactics that improve the library
                                nextPool.addAll(newLibs);

                                // Update the best library, if applicable
                                for (Library l: newLibs) {
                                    if (l.getOverallSize() <= bestLibrary.getOverallSize()) {
                                        bestLibrary = l;
                                    } else if (l.getOverallSize() == bestLibrary.getOverallSize()) {
                                        if (l.tactics.size() > bestLibrary.tactics.size()) {
                                            bestLibrary = l;
                                        }
                                    }
                                }
                            }
                        }
                    }

                    currentPool.clear();
                    while(currentPool.size() < BEAM_POOL_SIZE && nextPool.size() > 0) {
                        currentPool.add(nextPool.poll());
                    }
                }

                return bestLibrary;
            }
            default: {
                System.err.println("Sampling Type not yet supported");
                return new Library(corpus);
            }
        }
    }
}
