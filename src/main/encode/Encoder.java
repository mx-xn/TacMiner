package main.encode;

import main.config.BmConfig;
import main.config.Path;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.IntStream;

import org.json.*;

import static main.decode.utils.writeTo;
import static main.config.Path.trainingPath;

public class Encoder {
    public CoqProof proof;

    public Encoder(CoqProof proof) {
        this.proof = proof;
    }

    public static void initPGs(Collection<CoqProof> inputProofs) {
        for (CoqProof proof : inputProofs) {
            proof.initProofGraph();
        }
    }

    public static List<CoqProof> inputCoqScripts(String file) {
        StringBuilder fullFile = new StringBuilder("");
        // Read in JSON file
        try (Scanner myReader = new Scanner(new File(file))) {
            while (myReader.hasNextLine()) {
                fullFile.append(myReader.nextLine());
            }
        } catch (FileNotFoundException e) {
            System.out.println("cannot find file");
            e.printStackTrace();
        }

        List<CoqProof> proofs = new ArrayList<>();
        JSONArray jsonProofs = new JSONArray(fullFile.toString());

        for (int i = 0; i < jsonProofs.length(); i++) {
            JSONObject jsonProofObj = jsonProofs.getJSONObject(i);

            String lemma_name = "dummy_lemma";
            try {
                lemma_name = jsonProofObj.getString("lemma_name");
            } catch (Exception e) {
                lemma_name = "";
            }
            JSONArray jsonProof = jsonProofObj.getJSONArray("proof");

            List<CoqTactic> proof = new ArrayList<>();
            for (int j = 0; j < jsonProof.length(); j++) {
                JSONObject jsonTactic = jsonProof.getJSONObject(j);

                String sig = jsonTactic.getString("tactic_sig")
                        .replace(" , ", ", ")
                        .replace("[_o", "[ _o"); // Tactic signature
                String sig_no_out_arg = jsonTactic.getString("tactic_sig_no_out_arg").replace(" , ", ", ");

                // Tactic arguments
                JSONArray inputs = jsonTactic.getJSONArray("tactic_args");
                List<String> args = new ArrayList<>();
                for (int k = 0; k < inputs.length(); k++) {
                    args.add(inputs.getString(k));
                }

                // Tactic results
                JSONArray outputs = jsonTactic.getJSONArray("tactic_res");
                List<String> res = new ArrayList<>();
                for (int k = 0; k < outputs.length(); k++) {
                    // we need to flip the goals
                    // when gets to the hyps, flip all previous args
                    res.add(outputs.getString(k));
                }

                proof.add(new CoqTactic(j, sig, sig_no_out_arg, args, res));
            }
            proofs.add(new CoqProof(lemma_name, proof));
        }

        return proofs;
    }

    public static List<Integer> getTrainingProofIndices(BmConfig config, List<CoqProof> proofs) {
        if (!config.training) {
            return Arrays.stream(IntStream.range(0, proofs.size()).toArray()).boxed().toList();
        }
        List<Integer> res = new ArrayList<>();
        Set<String> trainingLemmas = new HashSet<>();
        // get the training data file
        // String filename = String.join("/", new String[]{config.domain, "training", config.topic + ".txt"});
        String filename = Path.trainingPath + config.topic + ".txt";
        try {
            // Read all lines from the file into a list of strings
            List<String> lines = Files.readAllLines(Paths.get(filename));

            // Print the resulting list of strings
            for (String line : lines) {
               trainingLemmas.add(line.trim());
            }
        } catch (IOException e) {
            // Handle exceptions that may occur while reading the file
            e.printStackTrace();
        }

        for (CoqProof p: proofs) {
            if (trainingLemmas.contains(p.lemma_name.trim())) {
                trainingLemmas.remove(p.lemma_name.trim());
                res.add(proofs.indexOf(p));
            }
        }

        return res;
    }

    public static void sampleRandomTrainingData(List<CoqProof> corpus, List<CoqProof> sample, double stopThresh, double stopBeginningThresh) {
        List<CoqProof> proofs = new ArrayList<>(corpus);
        proofs = proofs.stream().sorted((p1, p2) -> (p2.tactics.size() - p1.tactics.size())).toList();

        int numTacticsSample = 0;
        int numTacticsCorpus = 0;

        // for each proof,
        Map<String, Integer> renameMap = new HashMap<>();
        int numLemmas = 0;
        for (CoqProof p: proofs) {
            numTacticsCorpus += p.tactics.size();
        }
        double stopThreshold = stopThresh;
        double exceedsThreshold = stopBeginningThresh;

        for (CoqProof p: proofs) {
            if (p.lemma_name == "" || p.lemma_name == null) {
                p.lemma_name = "cus_lemma_" + (numLemmas++);
            }
            if (!renameMap.containsKey(p.lemma_name)) {
                renameMap.put(p.lemma_name, 0);
            }
            renameMap.put(p.lemma_name, renameMap.get(p.lemma_name) + 1);

            if (renameMap.get(p.lemma_name) > 1) {
                p.lemma_name = p.lemma_name + renameMap.get(p.lemma_name);
            }
        }

        List<Integer> sampleIDPool = new ArrayList<>();
        for (int i = 0; i < proofs.size(); i++) {
            sampleIDPool.add(i);
        }
        while ((double) numTacticsSample / numTacticsCorpus < stopThreshold) {
            int IndexPick = (int) (Math.random() * sampleIDPool.size());
            if (sampleIDPool.isEmpty()) break;
            int IdPick = sampleIDPool.remove(IndexPick);
            if ((double) (numTacticsSample + proofs.get(IdPick).tactics.size()) / numTacticsCorpus >= exceedsThreshold) continue;

            sample.add(proofs.get(IdPick));
            numTacticsSample += proofs.get(IdPick).tactics.size();
        }

        StringBuilder sb = new StringBuilder();

        // for each proof, get its name
        for (CoqProof s: sample) {
            sb.append(s.lemma_name).append("\n");
        }
    }
    //
    public static void sampleTrainingData(BmConfig config, List<CoqProof> corpus) throws IOException {
        List<CoqProof> sample = new ArrayList<>();
        List<CoqProof> proofs = new ArrayList<>(corpus);
        proofs = proofs.stream().sorted((p1, p2) -> (p2.tactics.size() - p1.tactics.size())).toList();

        double autoThreshold = 0.4;
        double tacticIncludeThreshold = 0.3;
        double tacticExcludeThreshold = 0.75;
        double tacticCountThreshold = 0.65;
        int numSimilarThreshold = 2;
        int numBranchesThreshold = 2;


        List<CoqProof> skip = new ArrayList<>();
        int numTacticsSample = 0;
        int numTacticsCorpus = 0;

        // for each proof,
        Map<String, Integer> renameMap = new HashMap<>();
        int numLemmas = 0;
        for (CoqProof p: proofs) {
            numTacticsCorpus += p.tactics.size();
        }

        double stopThreshold = config.stopThresh;
        double exceedsThreshold = config.stopThresh * 1.1;

        boolean stop = false;
        for (int g = 0; g < proofs.size(); g++) {
            CoqProof p = proofs.get(g);
            if (p.lemma_name == "" || p.lemma_name == null) {
                p.lemma_name = "cus_lemma_" + (numLemmas++);
            }
            if (!renameMap.containsKey(p.lemma_name)) {
                renameMap.put(p.lemma_name, 0);
            }
            renameMap.put(p.lemma_name, renameMap.get(p.lemma_name) + 1);

            if (renameMap.get(p.lemma_name) > 1) {
                p.lemma_name = p.lemma_name + renameMap.get(p.lemma_name);
            }

            if (stop) continue;
            if (skip.contains(p)) continue;
            if ((double) (numTacticsSample + p.tactics.size()) / numTacticsCorpus >= exceedsThreshold) continue;
            Map<String, Integer> pSigCount = p.getSigCount();

            // if 40% of it is just auto, skip it
            if ((double)pSigCount.getOrDefault("auto .", 0) / p.tactics.size() >= autoThreshold) {
                skip.add(p);
                continue;
            }

            // if it contains just one branch, skip it
            int numBranches = 1;
            for (CoqTactic t: p.tactics) {
                int numGoals = 0;
                for (CoqTactic.Prop out: t.outputs) {
                    if (out.type.equals(CoqTactic.PROP_TYPE.GOAL)) numGoals++;
                }
                if (numGoals > 1) {
                    numBranches++;
                }
            }
            if (numBranches < numBranchesThreshold) continue;

            // if it's just a singleton, skip it (unless if it's 40% longer than all of the remaining proofs)
            Set<String> signaturesP = pSigCount.keySet();
            int numSimilar = 0;
            boolean add = false;
            for (CoqProof p1: proofs) {
                if (p1.equals(p)) continue;
                if (sample.contains(p1)) continue;
                Map<String, Integer> p1SigCount = p1.getSigCount();
                Set<String> signaturesP1 = p1SigCount.keySet();
                Set<String> sigOverlaps = new HashSet<>(signaturesP);
                sigOverlaps.retainAll(signaturesP1);

                double sigOverlapPortion = (double) sigOverlaps.size() / signaturesP1.size();
                if (sigOverlapPortion < tacticIncludeThreshold) continue;

                double overlapTacCount = 0;
                double totalTacCount = 0;
                for (String sig: sigOverlaps) {
                    int pSigNumber = pSigCount.get(sig);
                    int p1SigNumber = p1SigCount.get(sig);

                    overlapTacCount += pSigNumber > p1SigNumber ? p1SigNumber : pSigNumber;
                    totalTacCount += p1SigNumber;
                }
                double sigCountOverlapPortion = overlapTacCount / totalTacCount;

                if (sigOverlapPortion >= tacticCountThreshold && sigCountOverlapPortion >= tacticExcludeThreshold) {
                    add = true;

                    // if the current proof is chosen, remove all other proofs that are too similar
                    skip.add(p1);
                } else if (!add && sigCountOverlapPortion >= tacticIncludeThreshold) {
                    numSimilar++;
                    if (numSimilar >= numSimilarThreshold) {
                        add = true;
                    }
                }
            }
            if (add) {
                sample.add(p);
                numTacticsSample += p.tactics.size();
            }
            // if we already found 40% of the proofs, stop process
            if ((double) numTacticsSample / numTacticsCorpus >= stopThreshold) stop = true;
        }
        if (stopThreshold >= 1) {
            sample = new ArrayList<>();
            for (CoqProof p: proofs) {
                sample.add(p);
            }
        }

        int i = -1;
        while ((double) numTacticsSample / numTacticsCorpus < stopThreshold && i < skip.size() - 1) {
            i++;
            if ((double) numTacticsSample / numTacticsCorpus >= exceedsThreshold) continue;
            sample.add(skip.get(i));
            numTacticsSample += skip.get(i).tactics.size();
        }
        // sort the proofs in the descending order of their length

        StringBuilder sb = new StringBuilder();

        // for each proof, get its name
        for (CoqProof s: sample) {
            sb.append(s.lemma_name).append("\n");
        }

        writeTo(sb.toString(), trainingPath + config.topic + ".txt");
    }
}
