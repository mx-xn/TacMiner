package main;

import main.config.BmConfig;
import main.encode.*;
import main.enumeration.Abstraction;
import main.enumeration.GraphEnumerator;
import main.eval.Ablation;
import main.eval.CompressionEval;
import main.proofgraph.ProofGraph;
import main.lib_assembler.*;

import java.io.*;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.*;
import java.util.stream.Collectors;
import java.nio.file.*;

import static main.config.BmConfig.*;
import static main.config.Paths.*;
import static main.encode.Encoder.sampleTrainingData;
import static main.enumeration.GraphEnumerator.floydWarshall;
import static main.eval.Ablation.AblationType.*;
import static main.eval.SyntacticBaseline.baselineExtractRaw;
import static main.maxsat.MaxSATUtil.tacticsToLtacScript;
import static main.maxsat.MaxSATUtil.writeTo;
// import static org.junit.jupiter.api.Assertions.assertEquals;

public class Main {
    public static int numRound;
    public static void main(String[] args) throws Exception, InterruptedException {
        if (args.length == 0)
            args = new String[] {"1200", "CompCert" , "Allocation", "100"};
        if (args.length < 4) {
            System.out.println("Not enough arguments were provided.");
            throw new IllegalArgumentException("need " + (4 - args.length) + " parameters!");
        }

        int timeoutInSec = Integer.parseInt(args[0]);
        int mode = 0;
        String domain = args[1];
        String topic = args[2];
        int trainPortion = Integer.parseInt(args[3]);
        String randSample = "False";
        boolean fixedTestData = mode == 4;

        int rounds = fixedTestData ? 5 : 1;
        for (int i = 0; i < rounds; i++) {
            numRound = i;
            List<BmConfig> configs = BmConfig.getBmConfig(timeoutInSec, mode, domain, topic, trainPortion, randSample);
            for (BmConfig config: configs) {
                List<CoqProof> proofs = Encoder.inputCoqScripts(config.getJsonFilename());

                // if we are in fixedTestData mode, we do things differently
                if (fixedTestData) {
                    // fix the testing indices
                    List<Integer> testingIndices = getFixedTestingIndices(proofs, i);
                    List<CoqProof> trainProofsCandidates = new ArrayList<>();
                    List<CoqProof> testingProofs = new ArrayList<>();
                    for (int p = 0; p < proofs.size(); p++) {
                        if (testingIndices.contains(p)) {
                            testingProofs.add(new CoqProof(proofs.get(p)));
                        } else {
                            trainProofsCandidates.add(proofs.get(p));
                        }
                    }

                    for (int n = startPortion; n <= endPortion; n+=5) {
                        // get corresponding train indices
                        config.updateStopThresh(n);
                        sampleTrainingData(config, trainProofsCandidates);

                        // remove useless proofs
                        List<Integer> trainingProofs = Encoder.getTrainingProofIndices(config, trainProofsCandidates);
                        List<CoqProof> proofsCopy = new ArrayList<>();
                        for (int p = 0; p < trainProofsCandidates.size(); p++) {
                            if (trainingProofs.contains(p)) proofsCopy.add(new CoqProof(trainProofsCandidates.get(p)));
                        }
                        proofsCopy.addAll(testingProofs);
                        runOnce(config, proofsCopy);
                    }
                    continue;
                }

                sampleTrainingData(config, proofs);
                switch (config.mode) {
                    case ENUMERATION:
                        runOnce(config, proofs);
//                    runOnce(config, proofs);
                        break;
                    case BASELINE:
                        baselineExtractRaw(config, proofs);
                        break;
                    case PRUNING_ABL:
                    case GRAMMAR_ABL:
                        Ablation ablP = new Ablation(config, proofs);
//                        ablP.runExperiments();
                        runOnce(config, proofs);
                        break;
                }
            }
        }
    }

    public static void runOnce(BmConfig selected, List<CoqProof> proofs) throws Exception {
        LibAssembler.Library lib = run(selected, proofs);
        String workingDirectory = Paths.get("").toAbsolutePath().toString();
        System.out.println("Current Working Directory: " + workingDirectory);
        if (selected.mode != BmConfig.Mode.ENUMERATION_SPLIT) {
            writeTo(lib.printDiagnostics(),
                    compressionEvalPath + selected.domain +
                            "-compressed/" + selected.topic +
                            "/" + selected.topic + "-" + String.format("%.2f", selected.stopThresh) + ".txt");
        }

        String expOutputLocation;
        if (selected.mode == BmConfig.Mode.ENUMERATION) {
            expOutputLocation = compressionEvalPath + selected.domain +
                    "-compressed/" + selected.topic +
                    "/csv/" + selected.topic + "-" + String.format("%.2f", selected.stopThresh) + ".csv";
            System.out.println("writing to " + expOutputLocation);
            writeTo(lib.printDiagnostics(selected, true), expOutputLocation);
        }

        if (selected.mode == BmConfig.Mode.ENUMERATION_SPLIT) {
            writeTo(lib.printDiagnostics(),
                    compressionEvalPath + selected.domain +
                            "-compressed/" + selected.topic +
                            "/round" + numRound + "/" + selected.topic + "-" + String.format("%.2f", selected.stopThresh) + ".txt");

            expOutputLocation = compressionEvalPath + selected.domain +
                    "-compressed/" + selected.topic +
                     "/" + selected.topic + "_" + numRound + ".csv";
            File csvFile = new File(expOutputLocation);
            // Check if the file exists; if not, create an empty file
            if (!csvFile.exists()) {
                csvFile.getParentFile().mkdirs(); // Create directories if they don't exist
                csvFile.createNewFile(); // Create the empty file
            }

            List<String> csvLines = Files.readAllLines(Paths.get(expOutputLocation));
            if (csvLines.isEmpty()) {
                csvLines.add("\n");
                csvLines.add("\n");
                csvLines.add("\n");
            }
            String[] newValues = lib.printDiagnostics(selected, false).split("\n");

            // Create a new list to hold the updated CSV lines
            List<String> updatedCsvLines = new ArrayList<>();
            for (int i = 0; i < csvLines.size(); i++) {
                String line = csvLines.get(i);
                line = line.trim() + ", " + newValues[i].trim(); // Append new value
                updatedCsvLines.add(line); // Add updated line to list
            }

            // Write the updated lines back to the CSV file
            writeTo(String.join("\n", updatedCsvLines), expOutputLocation);
        }
        System.out.println(lib.printDiagnostics());
    }

    public static LibAssembler.Library run(BmConfig config, List<CoqProof> proofs) throws IOException {
        // Part 1: Candidate Tactic Extraction
        // Read in proof corpus
//        List<CoqProof> proofs = Encoder.inputCoqScripts(config.inputJSON);

        // todo: get only the training proofs
        List<Integer> trainingProofs = Encoder.getTrainingProofIndices(config, proofs);

        Set<CoqProof> candidateTactics = new LinkedHashSet<>();
//        if (extractType.equals(MAXSAT))
//            candidateTactics = extractAllTacticsFromCorpus(proofs, config);
        List<Long> timePerTac = new ArrayList<>();
        List<CoqProof> compressedProofs = getLibCandidatesEnumeration(proofs, trainingProofs, candidateTactics,
                true, NONE, timePerTac, config.timeout, config.topic);

        if (config.mode == BmConfig.Mode.PRUNING_ABL || config.mode == BmConfig.Mode.GRAMMAR_ABL) {
            String fileName = compressionEvalPath + config.domain + "-compressed/ablation/" +
                    config.topic + "Ours.csv";
            // Write to CSV file
            StringBuilder sb = new StringBuilder("numTacs,Time\n");
            // Write the data rows
            for (int i = 0; i < timePerTac.size(); i++) {
                sb.append((i + 1) + "," + timePerTac.get(i) + "\n");
            }
            writeTo(sb.toString(), fileName);
        }

        LibAssembler.AssemblyType assmType = LibAssembler.AssemblyType.GREEDY;
        // filter out candidateTactics based on the compression power
//        if (assmType.equals(LibAssembler.AssemblyType.NONE)) {
//            System.out.println("num candidates before filtering: " + candidateTactics.size());
//            candidateTactics = removeLowCompressionTactics(candidateTactics, 0);
//            System.out.println("num candidates after filtering: " + candidateTactics.size());
//            int i = 0;
//            for (CoqProof c: candidateTactics) {
//                System.out.println("Ltac " + c.getRawString().replace("custom ", "custom" + (i++) + " "));
//            }
//            //todo
//        }


        // Part 2: Library Construction
        LibAssembler.Library library = null;
        // todo: we find the tactics to ignore in here

        library = LibAssembler.assembleLibraryForEnumerateGreedy(proofs, compressedProofs, candidateTactics, assmType, trainingProofs);

        int a = 0;
//        while (a < 20) {
            for (CoqProof proof : compressedProofs) {
                // if (proof.lemma_name.equals("Hoare_safe"))
                try {
                    String script = CompressionEval.graphToScript(proof);
                    System.out.println(script);
                } catch (Exception e) {
                    System.out.println(e);
                }
            }
//            a++;
//        }

        return library;
    }

    public static List<CoqProof> getLibCandidatesEnumeration(List<CoqProof> proofs, List<Integer> trainingProofIndices,
                                                             Set<CoqProof> candidateTactics, boolean greedyP, Ablation.AblationType ablationType,
                                                             List<Long> timePerTac, int timeOutInSeconds, String topic) {
        List<Abstraction> lib;
        List<CoqProof> currProofs = new ArrayList<>(proofs);
        Set<String> tacticRawString = new HashSet<>();
        List<Integer> ignoreTime = new ArrayList<>();
        GraphEnumerator.topic = topic;
        if (greedyP) {
            for (CoqProof p: proofs) {
                if (p.pgraph == null) p.pgraph = new ProofGraph(p.tactics);
            }
            long startTime = System.currentTimeMillis();
//            GraphEnumerator graphEnumerator;

            ExecutorService executorStart = Executors.newSingleThreadExecutor();

            // Task to be executed
            Callable<List<Abstraction>> getInitialLib = () -> {
                GraphEnumerator graphEnumerator;
                if (ablationType == NONE) {
                    graphEnumerator = new GraphEnumerator(proofs.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
                } else if (ablationType == GRAMMAR) {
                    graphEnumerator = new Ablation.GraphEnumeratorAblationGrammar(proofs.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
                } else {
                    graphEnumerator = new Ablation.GraphEnumeratorAblationPruning(proofs.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
                }
                return graphEnumerator.enumerateAbstractions(true);
            };

            List<Abstraction> currLib = new ArrayList<>();
            Future<List<Abstraction>> futureInitLib = null;
            try {
                // Submit the task to the executor
                futureInitLib = executorStart.submit(getInitialLib);
                // Wait for the task to complete, with a timeout of 2 seconds
                currLib = futureInitLib.get(timeOutInSeconds, TimeUnit.SECONDS);
            } catch (TimeoutException e) {
                System.out.println("compress timed out. Cancelling the task...");
                // Cancel the task if it times out
                if (futureInitLib != null) {
                    futureInitLib.cancel(true);
                }
            } catch (InterruptedException | ExecutionException e) {
                e.printStackTrace();
            } finally {
                // Shut down the executor
                executorStart.shutdown();
            }

            boolean stopNow = false;
            while (!currLib.isEmpty()) {
                if (stopNow) break;
                // Create an ExecutorService with a single thread
                ExecutorService executor = Executors.newSingleThreadExecutor();

                // Task to be executed
                List<Abstraction> finalCurrLib = currLib;
                List<CoqProof> finalCurrProofs = currProofs;
                Callable<List<CoqProof>> compress = () -> {
                    CoqProof t = finalCurrLib.get(0).customTactic;
                    String uniqueID = "custom" + candidateTactics.size();
                    String ltacName = t.lemma_name.replace("custom", uniqueID);

                    CoqProof tactic = new CoqProof(ltacName, t.tactics, tacticsToLtacScript(t.tactics, uniqueID).get(1), CoqProof.SequenceType.LTAC);

                    // each time we have a new tactic, we update the static vars reachTac and pathTac in CompressionEval
                    if (tactic.pgraph == null) tactic.pgraph = new ProofGraph(tactic.tactics);
                    int numV = tactic.pgraph.vertices.size();
                    CompressionEval.reachTac = new boolean[numV][numV];
                    CompressionEval.pathTac = new int[numV][numV];
                    floydWarshall(CompressionEval.reachTac, CompressionEval.pathTac, tactic.pgraph);

                    tactic.matches = t.matches;
                    candidateTactics.add(tactic);
                    long elapsedTime = System.currentTimeMillis() - startTime;
                    for (int minusTime: ignoreTime) {
                        elapsedTime -= minusTime;
                    }
                    if (tactic.tactics.size() > 50) {
                        int difference = (int) (timePerTac.isEmpty() ? 0 : timePerTac.get(timePerTac.size() - 1));
                        ignoreTime.add((int) (elapsedTime - difference));
                    } else if (!tacticRawString.contains(tactic.raw_string.split(" := ")[1])) {
                        tacticRawString.add(tactic.raw_string.split(" := ")[1]);
                        timePerTac.add(elapsedTime);
                    }
                    List<CoqProof> compressedProofs = new ArrayList<>();
                    List<Integer> compressedIndices = new ArrayList<>();
                    List<Integer> matchesGraphs = t.matches.keySet().stream().toList();
                    // Create an ExecutorService with a single thread

                    for (CoqProof p: finalCurrProofs) {
                        int i = finalCurrProofs.indexOf(p);
                        if (trainingProofIndices.size() == finalCurrProofs.size()) {
                            // if ran on entire corpus
                            if (!t.matches.keySet().contains(i)) {
                                compressedProofs.add(p);
                                continue;
                            }
                        } else if (trainingProofIndices.contains(i) && !t.matches.keySet().contains(i)) {
                            compressedProofs.add(p);
                            continue;
                        }
                        compressedProofs.add(CompressionEval.compressProof(p, tactic, i));
                        if (compressedProofs.get(i).tactics.size() < p.tactics.size()) {
                            compressedIndices.add(i);
                        }
                    }
                    return compressedProofs;
                };

                Future<List<CoqProof>> futureProofs = null;
                long timeout = timeOutInSeconds * 1000 - (System.currentTimeMillis() - startTime);
                try {
                    // Submit the task to the executor
                    futureProofs = executor.submit(compress);
                    // Wait for the task to complete, with a timeout of 2 seconds
                    List<CoqProof> compressedProofs = futureProofs.get(timeout, TimeUnit.MILLISECONDS);
                    currProofs = compressedProofs;
                } catch (TimeoutException e) {
                    System.out.println("compress timed out. Cancelling the task...");
                    // Cancel the task if it times out
                    if (futureProofs != null) {
                        futureProofs.cancel(true);
                    }
                    stopNow = true;
                } catch (InterruptedException | ExecutionException e) {
                    e.printStackTrace();
                } finally {
                    // Shut down the executor
                    executor.shutdown();
                }
                if (stopNow) break;

                // if gets here, currProofs are already updated
                ExecutorService executor1 = Executors.newSingleThreadExecutor();
                List<CoqProof> finalCurrProofsNew = currProofs;
                Callable<List<Abstraction>> getNewLib = () -> {
                    GraphEnumerator graphEnumeratorNew;
                    if (ablationType == NONE) {
                        graphEnumeratorNew = new GraphEnumerator(finalCurrProofsNew.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
                    } else if (ablationType == GRAMMAR) {
                        graphEnumeratorNew = new Ablation.GraphEnumeratorAblationGrammar(finalCurrProofsNew.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
                    } else {
                        graphEnumeratorNew = new Ablation.GraphEnumeratorAblationPruning(finalCurrProofsNew.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
                    }
                    return graphEnumeratorNew.enumerateAbstractions(true);
                };

                Future<List<Abstraction>> futureLib = null;
                timeout = timeOutInSeconds * 1000 - (System.currentTimeMillis() - startTime);
                try {
                    // Submit the task to the executor
                    futureLib = executor1.submit(getNewLib);
                    // Wait for the task to complete, with a timeout of 2 seconds
                    currLib = futureLib.get(timeout, TimeUnit.MILLISECONDS);
                } catch (TimeoutException e) {
                    System.out.println("compress timed out. Cancelling the task...");
                    // Cancel the task if it times out
                    if (futureLib != null) {
                        futureLib.cancel(true);
                    }
                    stopNow = true;
                } catch (InterruptedException | ExecutionException e) {
                    e.printStackTrace();
                } finally {
                    // Shut down the executor
                    executor1.shutdown();
                }
            }
        } else {
            for (CoqProof p : proofs) {
                if (p.pgraph == null) p.pgraph = new ProofGraph(p.tactics);
            }
            GraphEnumerator graphEnumerator;
            if (ablationType == NONE) {
                graphEnumerator = new GraphEnumerator(proofs.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
            } else if (ablationType == GRAMMAR) {
                graphEnumerator = new Ablation.GraphEnumeratorAblationGrammar(proofs.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
            } else {
                graphEnumerator = new Ablation.GraphEnumeratorAblationPruning(proofs.stream().map(p -> p.pgraph).collect(Collectors.toList()), trainingProofIndices);
            }
            lib = graphEnumerator.enumerateAbstractions(false);
            candidateTactics.addAll(
                    lib.stream().sorted((a1, a2) -> Integer.compare(a2.utility - a2.utilityTraining, a1.utility - a1.utilityTraining))
                            .map(a -> a.customTactic).collect(Collectors.toList()));
        }
        return currProofs;
    }

    public static List<Integer> getFixedTestingIndices(List<CoqProof> proofs, int numRound) {
        List<Integer> res = new ArrayList<>();
        int seed = BmConfig.seeds[numRound];

        Random generator = new Random(seed);
        int pID;

        // get sizes of all corpus
        int totalSize = 0;
        for (CoqProof p: proofs) {
            totalSize += p.tactics.size();
        }

        int testSize = 0;
        while ((double) testSize / totalSize < BmConfig.fixedTestingPortion) {
            pID = generator.nextInt(proofs.size());
            res.add(pID);
            testSize += proofs.get(pID).tactics.size();
        }

        return res;
    }
};

