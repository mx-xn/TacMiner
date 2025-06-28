package main.lib_assembler;

import main.config.BmConfig;
import main.encode.CoqProof;
import main.encode.Encoder;
import main.eval.SyntacticBaseline.*;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static main.eval.SyntacticBaseline.*;
import static main.decode.utils.*;

public class LibAssemblerBaseline {
    public enum AssemblyType {
        EXHAUSTIVE,
        EXH_COMPRESS,
        GREEDY,
    }

    public static class LibraryBaseline implements Comparable<LibraryBaseline> {
        public List<BaselineProof> corpus;
        public List<BaselineProof> tactics;
        List<Integer> trainingIndices;
        public List<BaselineProof> unusedTacs;

        private int corpusSize;
        private int trainingSize;
        private int compressedSize;
        private int testingCompressedSize;
        private int librarySize;
        private Map<String, List<Integer>> tacOccurrences = new HashMap<>();

        private int corpusHashCode;

        public LibraryBaseline(List<BaselineProof> corpus){
            this.corpus = new ArrayList<>();
            for (BaselineProof each: corpus) {
                this.corpus.add(new BaselineProof(each));
            }
            this.tactics = new ArrayList<>();

            this.corpusHashCode = corpus.hashCode();

            this.corpusSize = this.compressedSize = this.librarySize = 0;
            // Populate sizes
            for (int i = 0; i < this.corpus.size(); i++) {
                BaselineProof each = this.corpus.get(i);
                this.corpusSize += each.size();
                this.compressedSize += each.size();
            }
        }

        public LibraryBaseline(LibraryBaseline o) {
            this.corpus = new ArrayList<>();
            for (BaselineProof each: o.corpus) {
                this.corpus.add(new BaselineProof(each));
            }
            this.tactics = new ArrayList<>();
            for (BaselineProof each: o.tactics) {
                this.tactics.add(new BaselineProof(each));
            }
            this.corpusSize = o.corpusSize;
            this.compressedSize = o.compressedSize;
            this.testingCompressedSize = o.testingCompressedSize;
            this.librarySize = o.librarySize;
            this.unusedTacs = new ArrayList<>();
            for (BaselineProof each: o.unusedTacs) {
                this.unusedTacs.add(new BaselineProof(each));
            }

            this.corpusHashCode = o.corpusHashCode;
            this.trainingIndices = o.trainingIndices;
            this.trainingSize = o.trainingSize;
            this.tacOccurrences = o.tacOccurrences;
        }

        public void setTrainingIndices(List<Integer> trainingIndices) {
            this.trainingIndices = trainingIndices;
            int size = 0;
            for (int i: this.trainingIndices) {
                size += this.corpus.get(i).size();
            }
            this.trainingSize = size;

            int testingSize = 0;
            for (int i = 0; i < this.corpus.size(); i++) {
                if (!trainingIndices.contains(i) || trainingIndices.size() == this.corpus.size()) {
                    testingSize += this.corpus.get(i).size();
                }
            }
            this.testingCompressedSize =  testingSize;
        }

        public int getOverallSize() {
            return compressedSize + librarySize;
        }

        public int getTestingCompressedSize() {
            return testingCompressedSize;
        }

        public double getCompression() {
            return (double) corpusSize / (compressedSize + librarySize);
        }

        public void validCheck(List<String> originalProofs, List<CoqProof> coqProofs, List<BaselineProof> originalCoqProofs, BmConfig config) throws IOException {
            this.testingCompressedSize = 0;
            for (int p = 0; p < this.corpus.size(); p++) {
                if (trainingIndices.size() < this.corpus.size() && trainingIndices.contains(p)) continue;
                this.testingCompressedSize += this.corpus.get(p).size();
            }
            String content = new String(Files.readAllBytes(Paths.get(config.getInputFilename())));
            String outputName = main.config.Path.baselineIntermediatePath + config.domain + "/" + config.topic + "_tacs_verified.txt";

            List<String> newProofs = new ArrayList<>();
            for (String p: originalProofs) {
                newProofs.add(new String(p));
            }

            List<BaselineProof> remove = new ArrayList<>();
            // for each current tactic, try to refactor the proof with the tactic
            this.tacOccurrences = new HashMap<>();
            List<String> newPs = new ArrayList<>();
            for (BaselineProof t: this.tactics) {
                boolean canRefactor = false;
                for (int i = 0; i < this.corpus.size(); i++) {
                    if (this.trainingIndices.size() != this.corpus.size() && this.trainingIndices.contains(i)) continue;
                    BaselineProof p = this.corpus.get(i);

                    List<Integer> usedIndices = new ArrayList<>();
                    for (int j = 0; j < p.completeTokens.size(); j++) {
                        if (p.cleanTokens.get(j).equals(t.name)) {
                            usedIndices.add(j);
                        }
                    }
                    if (usedIndices.isEmpty()) continue;

                    // try refactoring
                    String newP = refactor(originalProofs.get(i), originalCoqProofs.get(i), this.corpus.get(i), t);
                    String newContent = content.replace(originalProofs.get(i).trim(), newP.trim());

                    // count number of occurrences of t in newContent
                    int numOccurBase = this.corpus.get(i).cleanTokens.stream().filter(tk -> tk.equals(t.name)).toList().size();

                    // only check if valid if current proof is in testing corpus
                    boolean validCoqScript = isValidCoqScript(newContent, t, config, this.tactics);
                    File file = new File(outputName);
                    file.delete();
                    if (validCoqScript) {
                        newPs.add(coqProofs.get(i).lemma_name + ":");
                        newPs.add(newP);
                        if (!this.tacOccurrences.containsKey(t.name)) {
                            this.tacOccurrences.put(t.name, new ArrayList<>());
                        }
                        for (int k = 0; k < numOccurBase; k++) {
                            this.tacOccurrences.get(t.name).add(i);
                        }
                        // if successful refactoring, do nothing
                        canRefactor = true;
                    } else {
                        // if unsuccessful refactoring, update the compressionRate by adding the number of usage * (tacSize - 1)
                        this.testingCompressedSize += (t.size() - 1) * numOccurBase;
                    }
                }

                // if nothing can be refactored, remove the tactic
                if (!canRefactor) remove.add(t);
            }

            for (BaselineProof t: remove) {
                this.tactics.remove(t);
            }
        }

        public static boolean isValidCoqScript(String coqContent, BaselineProof cusTac, BmConfig config, List<BaselineProof> tactics) throws IOException {
            // write to resources
            // get all proofs
            List<CoqProof> proofs = Encoder.inputCoqScripts(config.getJsonFilename());
            List<String> lemmaNames = proofs.stream().map(p -> p.lemma_name).toList();
            List<String> contractedProofs = retrieveProofsForRefactoring(coqContent);

            StringBuilder sb = new StringBuilder("");

            StringBuilder allTactics = new StringBuilder("");

            for (int i = 0; i < lemmaNames.size(); i++) {
                // if current lemma uses custom tactic, and custom tactic is not in allTacs, it was ignored, so add here
                if (!lemmaNames.get(i).contains("_ignore") && contractedProofs.get(i).contains("custom")) {
                    List<String> commands = new ArrayList<>();

                    // Define regex pattern to match "custom" followed by digits
                    Pattern pattern = Pattern.compile("custom_tac\\d+ ");
                    Matcher matcher = pattern.matcher(contractedProofs.get(i));

                    // Find all matches and add them to the list
                    while (matcher.find()) {
                        commands.add(matcher.group());
                    }

                    for (String tacName: commands) {
                        if (sb.indexOf("Ltac " + tacName) == -1) {
                            // find the corresponding tactics and add to here.
                            for (BaselineProof candTac: tactics) {
                                if (tacName.contains(candTac.name + " ")) {
                                    sb.append(candTac.cusTacticScript()).append("\n").append("\n");
                                    break;
                                }
                            }
                        }
                    }
                }
                if (lemmaNames.get(i).contains("_ignore")) {
                    sb.append(lemmaNames.get(i).split("\\_ignore")[0]).append('\n');
                } else {
                    sb.append(lemmaNames.get(i)); sb.append('\n');
                }
                sb.append(contractedProofs.get(i)); sb.append('\n');
            }
            String contractedScript = sb.toString();

            // Write valid tactics to file
            String inputV = config.getInputFilename();
            String outputName = main.config.Path.baselineIntermediatePath +
                    config.domain + "/" + config.topic + "_tacs.txt";
            writeTo(inputV + "\n-----\n" + inputV.replace(".v", "_compr.v") + "\n-----\n" + allTactics.toString() + "-----\n" + contractedScript,
                   outputName);

            try {
                // Use python script to verify proofs
                String command = "/bin/bash";
                // String scriptPath = "./runVerifier.sh";

                String targetDir = System.getProperty("user.dir") + "/src/python/";
                String targetName = "runVerifier_" + config.topic + config.mode + ".sh";

                // Define the full path to the script
                Path tempScriptPath = Paths.get(targetDir + targetName);

                // Make the script executable
                String script = new String(Files.readAllBytes(Paths.get(targetDir + "runVerifier.sh")));
                // Replace placeholders with actual values
                script = script.replace("{{filename}}", config.topic);
                script = script.replace("{{domain}}", config.domain);

                // Write the modified script to the target directory
                Files.write(tempScriptPath, script.getBytes());
                tempScriptPath.toFile().setExecutable(true);

                Files.write(tempScriptPath, script.getBytes());

                // Create a ProcessBuilder with the specified command
                ProcessBuilder processBuilder = new ProcessBuilder(command, targetName);
                processBuilder.directory(new File(System.getProperty("user.dir")
                        + "/src/python/"));

                // Start the process
                Process process = processBuilder.start();

                // Wait for the process to finish
                int exitcode = process.waitFor();

                 // Clean up: delete the temporary script file
                Files.delete(tempScriptPath);
            } catch (IOException | InterruptedException e) {
                 e.printStackTrace();
            }

             // Read in successful proofs
            boolean valid = false;

            try (BufferedReader br = new BufferedReader(new FileReader(outputName.replace(".txt", "_verified.txt")))) {
                String line;
                if ((line = br.readLine()) != null) {
                    if (line.equals("T")) {
                        valid = true;
                    }
                }
            } catch (IOException e) {
                e.printStackTrace();
            }

            return valid;
        }

        public static String refactor(String proof, BaselineProof oriCoqProof, BaselineProof newCoqProof, BaselineProof tactic) {
            // map each proof token index to its end index in the string
            Map<Integer, Integer> tokenToStringEnd = new HashMap<>();
            Map<Integer, Integer> tokenToStringStart = new HashMap<>();
            proof = processBrackets(proof);
            StringBuilder currProof = new StringBuilder(processBrackets(proof));
            for (int i = 0; i < oriCoqProof.completeTokens.size(); i++) {
                String token = oriCoqProof.completeTokens.get(i);
                int start = currProof.indexOf(token);
                tokenToStringEnd.put(i, start + token.length());
                tokenToStringStart.put(i, start);
                String replacement = new String();
                for (int r = 0; r < token.length(); r++) {
                    replacement += "*";
                }
                if (start == -1) {
                    System.out.println();
                }
                currProof = currProof.replace(start, start + token.length(), replacement);
            }

            int oriPtr = 0;
            int newPtr = 0;
            StringBuilder newProofSB = new StringBuilder();
            while (oriPtr < oriCoqProof.size() && newPtr < newCoqProof.size()) {
                // appending each token to a new string
                String oriToken = oriCoqProof.completeTokens.get(oriPtr);
                String newToken = newCoqProof.completeTokens.get(newPtr);

                if (oriToken.equals(newToken)) {
                    newProofSB.append(proof.substring(tokenToStringEnd.getOrDefault(oriPtr - 1, 0), tokenToStringEnd.get(oriPtr)));
                    oriPtr++;
                    newPtr++;
                } else {
                    // for each index where oriCoqProof and newCoqProof are different,
                    // ignore the corresponding section of the string, and replace with the custom tactic

                    // append proof[lastEnd, currStart]
                    newProofSB.append(proof.substring(tokenToStringEnd.getOrDefault(oriPtr - 1, 0),
                                                      tokenToStringStart.get(oriPtr)))
                            .append(newCoqProof.completeTokens.get(newPtr));
                    // count length of tactic
                    oriPtr += tactic.size();
                    newPtr++;
                }
            }

            return newProofSB.toString() + ".\n";
        }

        public List<LibraryBaseline> addAndCompress(BaselineProof tactic, AssemblyType type) {
            List<BaselineProof> compressedCorpus = new ArrayList<>();
            List<LibraryBaseline> res = new ArrayList<>();

            int candidateSize = 0;
            int testingCandidateSize = 0;
            for (int i = 0; i < corpus.size(); i++) {
                // compress current proof with the extracted tactic
                BaselineProof compressed = new BaselineProof(corpus.get(i));

                compressed.compress(tactic);
                // add the compressed proof to the compressedCorpus
                compressedCorpus.add(compressed);

                // add the size of the compressed proof
                candidateSize += compressed.size();
                if (!trainingIndices.contains(i) || trainingIndices.size() == corpus.size()) {
                    testingCandidateSize += compressed.size();
                }
            }

            List<List<BaselineProof>> libCopies = new ArrayList<>();
            if (type.equals(AssemblyType.EXH_COMPRESS)) {
                // actually try to compress tactics with tactic
                libCopies = compressLibTacs(tactic, new ArrayList<>(this.tactics));
            } else {
                libCopies = Arrays.asList(this.tactics);
            }

            for (List<BaselineProof> libCopy : libCopies) {
                int libSizeDecrease = 0;
                LibraryBaseline lib = new LibraryBaseline(this);

                if (candidateSize < this.compressedSize) {
                    // This tactic is beneficial, so let's keep it
                    lib.corpus = compressedCorpus; // Compress corpus
                    lib.tactics = new ArrayList<>(libCopy);
                    lib.tactics.add(tactic); // Add to library

                    lib.compressedSize = candidateSize; // update sizes
                    lib.testingCompressedSize = testingCandidateSize;
                    lib.librarySize += (tactic.size() - libSizeDecrease);

                    res.add(lib);
                }
            }

            return res;
        }

        public String printTactics() {
            StringBuilder sb = new StringBuilder();
            int i = 0;
            for (BaselineProof tac: this.tactics) {
                sb.append(tac.cusTacticScript()).append("\n");
                i++;
            }
            return sb.toString();
        }

        public String printCompressionRate() {
            StringBuilder sb = new StringBuilder("compression_rate\n");
            int testingOriSize = this.corpusSize - this.trainingSize;
            sb.append(String.format("%.2f", (double) testingOriSize / this.testingCompressedSize)).append("\n");

            return sb.toString();
        }

        public String printTacticsStats() {
            int libSize = 0;
            int maxTacSize = 0;
            for (BaselineProof t: this.tactics) {
                if (t.completeTokens.size() > maxTacSize)
                    maxTacSize = t.completeTokens.size();
                libSize += t.completeTokens.size();
            }
            int numTotalApplications = this.tacOccurrences.values().stream().map(l -> l.size()).toList()
                    .stream().reduce(0, Integer::sum);
            StringBuilder sb = new StringBuilder();
            return sb.toString() + 
                    "tactics_learned,avg_tactic_size,max_tactic_size,tactic_usage_count\n" +
                    this.tactics.size() + "," +
                    String.format("%.2f", (double) libSize / this.tactics.size()) + "," +
                    maxTacSize + "," +
                    numTotalApplications + "\n";
        }

        @Override
        public int compareTo(LibraryBaseline o) {
            if (this.corpusSize != o.corpusSize) {
                System.err.println("Different proof corpuses: libraries not comparable");
                return 0;
            }
            return Integer.compare(this.getOverallSize(), o.getOverallSize());
        }
    }


    public static List<List<BaselineProof>> compressLibTacs(BaselineProof tactic, List<BaselineProof> libTacs) {
        List<List<BaselineProof>> res = new ArrayList<>();
        libTacs = new ArrayList<>(libTacs);
        res.add(libTacs);
        List<BaselineProof> compressedTactics = new ArrayList<>();

        boolean compressible = false;
        for (BaselineProof tacToCompress: libTacs) {
            int i = 0;
            String first = tactic.cleanTokens.get(0);
            int indexDecrease = 0;

            BaselineProof copy = new BaselineProof(tacToCompress);
            System.out.println("tactic to compress: " + tacToCompress.prettyPrint() + ", size: " + tacToCompress.size());
            while (copy.cleanTokens.subList(i, copy.cleanTokens.size()).contains(first)) {
                // check if remaining is also a match
                int startIndex = copy.cleanTokens.subList(i, copy.cleanTokens.size()).indexOf(first) + i;
                if (startIndex + tactic.size() > copy.size()) break;
                BaselineProof match = copy.getSubproof(startIndex, tactic.size());
                if (match.cleanCompleteTokens.equals(tactic.cleanCompleteTokens)) {
                    // if remaining a match, try to unify the arguments, update i -> i + tactic.size
                    if (canUnify(match.args, tactic.args)) {
                        // replace
                        compressible = true;
                        tacToCompress.compressSection(startIndex - indexDecrease, tactic, match.args);
                        System.out.println("after compress: " + tacToCompress.completeTokens + ", size: " + tacToCompress.size() );
                        i = startIndex + tactic.size();
                        indexDecrease += (tactic.size() - 1);
                        continue;
                    }
                }

                // if remaining not a match, or unification does not work, keep going
                i++;
            }
            System.out.println("adding tactic of size " + tacToCompress.size() + ", " + tacToCompress.prettyPrint());
            compressedTactics.add(tacToCompress);
        }

        if (compressible) res.add(compressedTactics);

        System.out.println("res size: " + res.size());
        return res;
    }

    public static LibraryBaseline assembleLibraryBaseline(List<BaselineProof> corpus, List<BaselineProof> customTacs, AssemblyType type, List<Integer> trainingIndices) {
        customTacs = customTacs.stream().sorted((t1, t2) -> Integer.compare(t2.size(), t1.size())).collect(Collectors.toList());
        // filter duplicate and empty customTac
        switch (type) {
            case EXHAUSTIVE: case EXH_COMPRESS: {
                PriorityQueue<LibraryBaseline> currPool = new PriorityQueue<>();

                LibraryBaseline currLib = new LibraryBaseline(corpus);
                currLib.setTrainingIndices(trainingIndices);
                currLib.tactics = new ArrayList<>();
                currLib.unusedTacs = new ArrayList<>(customTacs);
                currPool.add(currLib);
                LibraryBaseline bestLib = currLib;
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
                    BaselineProof currTactic = currLib.unusedTacs.remove(0);
                    LibraryBaseline newLib = new LibraryBaseline(currLib);
                    List<LibraryBaseline> newLibs = newLib.addAndCompress(currTactic, type);
                    if (!newLibs.isEmpty()) {
                        System.out.println("adding new libs");
                        currPool.addAll(newLibs);
                    }
                }
                return bestLib;
            } case GREEDY: {
                List<LibraryBaseline> libs = new ArrayList<>();
                LibraryBaseline currLib = new LibraryBaseline(corpus);
                currLib.setTrainingIndices(trainingIndices);
                currLib.tactics = new ArrayList<>();
                currLib.unusedTacs = new ArrayList<>(customTacs);
                int bestCompressedSize = currLib.getTestingCompressedSize();
                LibraryBaseline bestLib = currLib;
                libs.add(currLib);

                List<BaselineProof> availableTacs = new ArrayList<>(customTacs);

                // for each library in libs, try to find the best tactic and add, and keep going
                List<LibraryBaseline> bestLibs = new ArrayList<>();
                for (LibraryBaseline lib: libs) {
                    boolean stopEarly = false;
                    // make sure we've trying adding each of them
                    for (int i = 0; i < customTacs.size(); i++) {
                        // find the best one
                        int bestSize = lib.getTestingCompressedSize();
                        LibraryBaseline bestCurrLib = lib;
                        BaselineProof bestTac = null;
                        for (BaselineProof tac: availableTacs) {
                            LibraryBaseline copy = new LibraryBaseline(lib);
                            List<LibraryBaseline> compressedLibs = copy.addAndCompress(tac, type);
                            for (LibraryBaseline compressedLib : compressedLibs) {
                                if (compressedLib.getTestingCompressedSize() < bestSize) {
                                    bestSize = compressedLib.getTestingCompressedSize();
                                    bestCurrLib = compressedLib;
                                    bestTac = tac;
                                }
                            }
                        }
                        if (bestTac == null) {
                            // no tactic applicable, return
                            bestLibs.add(new LibraryBaseline(bestCurrLib));
                            stopEarly = true;
                        } else {
                            bestCurrLib.unusedTacs.remove(bestTac);
                            availableTacs.remove(bestTac);
                            lib = bestCurrLib;
                        }
                    }
                    if (!stopEarly && !bestLibs.contains(lib)) {
                        bestLibs.add(lib);
                    }
                }

                for (LibraryBaseline libCandidate : bestLibs) {
                    if (libCandidate.getTestingCompressedSize() < bestCompressedSize) {
                        bestCompressedSize = libCandidate.getTestingCompressedSize();
                        bestLib = libCandidate;
                    }
                }
                return bestLib;
            }
            default: {
                System.err.println("Sampling Type not yet supported");
                return new LibraryBaseline(corpus);
            }
        }
    }
}
