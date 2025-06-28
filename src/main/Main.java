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
import static main.config.Path.*;
import static main.decode.utils.*;
import static main.encode.Encoder.sampleTrainingData;
import static main.enumeration.GraphEnumerator.floydWarshall;
import static main.eval.Ablation.AblationType.*;
import static main.eval.SyntacticBaseline.baselineExtractRaw;

public class Main {
    public static int numRound;
    public static void main(String[] args) throws Exception, InterruptedException {
        // arguments: mode (0: enumeration, 1: baseline, 2: pruning abl, 3: grammar abl, 4: fixed test data (RQ4)), 
        //            domain, topic, trainPortion
        if (args.length == 0)
            // args = new String[] {"1200", "coq-art" , "IndPred", "100"};
            // mode, domain, topic, timeout-in-seconds
            args = new String[] {"1", "coq-art" , "parsing", "3600", "100"};
        if (args.length < 5) {
            System.out.println("Not enough arguments were provided.");
            throw new IllegalArgumentException("need " + (4 - args.length) + " parameters!");
        }

        int mode = Integer.parseInt(args[0]);
        String domain = args[1];
        String topic = args[2];
        int timeoutInSec = Integer.parseInt(args[3]);
        int trainPortion = Integer.parseInt(args[4]);

        int rounds = (mode == 4) ? 5 : 1;
        for (int i = 0; i < rounds; i++) {
            numRound = i;
            List<BmConfig> configs = BmConfig.getBmConfig(timeoutInSec, mode, domain, topic, trainPortion);
            for (BmConfig config: configs) {
                List<CoqProof> proofs = Encoder.inputCoqScripts(config.getJsonFilename());

                // if we are in fixedTestData mode, we do things differently
                if (config.mode == BmConfig.Mode.ENUMERATION_SPLIT) {
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
                    // continue;
                } else {
                    sampleTrainingData(config, proofs);
                    switch (config.mode) {
                        case ENUMERATION:
                            runOnce(config, proofs);
                            break;
                        case BASELINE:
                            baselineExtractRaw(config, proofs);
                            break;
                        case PRUNING_ABL:
                        case GRAMMAR_ABL:
                            Ablation ablP = new Ablation(config, proofs);
                            runOnce(config, proofs);
                            ablP.runExperiments();
                            break;
                    }
                }
            }
        }
    }

    public static void runOnce(BmConfig selected, List<CoqProof> proofs) throws Exception {
        LibAssembler.Library lib = run(selected, proofs);
        if (selected.mode == BmConfig.Mode.ENUMERATION) {
            if (!selected.training) {
                // if no training, running exp RQ1
                String tacsOutputLocation = evalPath + RQ1 + "tacminer/tactics/" + selected.topic + ".txt";
                writeTo(lib.printTactics(), tacsOutputLocation);

                String statsOutputLocation = evalPath + RQ1 + "tacminer/" + selected.topic + ".csv";
                writeTo(lib.printTacticsStats(), statsOutputLocation);
            } else {
                // else, running exp RQ2
                String tacsOutputLocation = evalPath + RQ2 + "tacminer/tactics/" + selected.topic + ".txt";
                writeTo(lib.printTactics(), tacsOutputLocation);

                String cpOutputLocation = evalPath + RQ2 + "tacminer/" + selected.topic + ".csv";
                writeTo(lib.printCompressionRate(), cpOutputLocation);
            }
        }

        if (selected.mode == BmConfig.Mode.ENUMERATION_SPLIT) {
            StringBuilder sb = new StringBuilder();
            boolean clear = false;
            if (selected.stopThresh == 0.2) {
                // if at the lowest training portion, we denote the number of round currently in
                if (numRound == 0) {
                    // if at the first round, we add the header
                    List<String> header = Arrays.asList("0.20", "0.25", "0.30", "0.35", "0.40",
                            "0.45", "0.50", "0.55", "0.60", "0.65", "0.70",
                            "0.75", "0.80", "0.85", "0.90", "0.95", "1.00");
                    sb.append("ComprRate-per-TrainPortion, ").append(String.join(", ", header)).append("\n");
                    clear = true;
                }
                sb.append("CR_round" + (numRound + 1) + ", ");
            }
            sb.append(String.format("%.2f", (double) (lib.getCorpusSize() - lib.getTrainingSize()) / lib.getTestingCompressedSize()));
            if (selected.stopThresh == 1) {
                // if at the highest training portion, we add a new line
                sb.append("\n");
            } else {
                sb.append(", ");
            }
            writeTo(sb.toString(), evalPath + RQ4 + selected.topic + ".csv", clear);
        }
    }

    public static LibAssembler.Library run(BmConfig config, List<CoqProof> proofs) throws IOException {
        System.out.println("Extracting tactics using tacminer for Topic: " + config.topic);
        // Part 1: Candidate Tactic Extraction
        List<Integer> trainingProofs = Encoder.getTrainingProofIndices(config, proofs);

        Set<CoqProof> candidateTactics = new LinkedHashSet<>();
        List<Long> timePerTac = new ArrayList<>();
        List<CoqProof> compressedProofs = getLibCandidatesEnumeration(proofs, trainingProofs, candidateTactics,
                true, NONE, timePerTac, config.timeout, config.topic);

        if (config.mode == BmConfig.Mode.PRUNING_ABL || config.mode == BmConfig.Mode.GRAMMAR_ABL) {
            String fileName = evalPath + RQ5 + "tacminer/" + config.domain + "/" + config.topic + ".csv";
            // Write to CSV file
            StringBuilder sb = new StringBuilder("numTacs,Time\n");
            // Write the data rows
            for (int i = 0; i < timePerTac.size(); i++) {
                sb.append((i + 1) + "," + timePerTac.get(i) + "\n");
            }
            writeTo(sb.toString(), fileName);
        }

        LibAssembler.AssemblyType assmType = LibAssembler.AssemblyType.GREEDY;

        // Part 2: Library Construction
        LibAssembler.Library library = null;
        System.out.println("assembling library ... ");
        library = LibAssembler.assembleLibraryForEnumerateGreedy(proofs, compressedProofs, candidateTactics, assmType, trainingProofs);

        for (CoqProof proof : compressedProofs) {
            try {
                String script = CompressionEval.graphToScript(proof);
            } catch (Exception e) {
                System.out.println(e);
            }
        }

        System.out.println("finished assembling tactic-library for: " + config.topic); 
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
                    // List<Integer> matchesGraphs = t.matches.keySet().stream().toList();
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

