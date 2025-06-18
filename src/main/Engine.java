package main;

import main.config.BmConfig;
import main.encode.*;
import main.eval.CompressionEval;
import main.maxsat.*;
import main.proofgraph.*;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.stream.Collectors;

import static main.config.Paths.*;
import static main.maxsat.MaxSATUtil.*;

public class Engine {
    public String filename;
    List<CoqProof> lemmas;
    MaxSatEncoder mse;
    public List<CoqProof> mcsScript;
    List<String> originalScriptList;
    List<String> contractedScriptList;

    long timeConvert = 0;
    long timeEncodeRd1 = 0;
    long timeSolveRd1 = 0;
    long timeEncodeRd2 = 0;
    long timeSolveRd2 = 0;
    long timeDecodeToGraph = 0;
    long timeDecodeToScript = 0;
    long totalTime = 0;
    BmConfig config;

    public Engine(List<ProofGraph> pgs, BmConfig config, boolean pgFlag) {
        this.lemmas = new ArrayList<>();
        for (ProofGraph pg: pgs) {
            CoqProof cp = new CoqProof("l" + this.lemmas.size(), pg.vertices, "", CoqProof.SequenceType.PROOF);
            cp.initProofGraph();
            this.lemmas.add(cp);
        }

        this.config = config;
//        this.inputGraphs = pgs;
    }
    public Engine(List<CoqProof> inputProofList, BmConfig config) {
        this.lemmas = inputProofList;
        this.config = config;
        initGraphs(inputProofList);
    }

    public void initGraphs(List<CoqProof> inputProofList) {
        long begin = System.currentTimeMillis();
        Encoder.initPGs(inputProofList);
        long end = System.currentTimeMillis();
        this.timeConvert += (end - begin);
    }

    public void encodeRd1() throws IOException {
        long begin = System.currentTimeMillis();
        this.mse = new MaxSatEncoder(this.lemmas);
        String maxSATInput = this.mse.encodeSAT(false);
        writeTo(maxSATInput, maxsatFilesPath + "maxsatInput.txt");
        long end = System.currentTimeMillis();
        this.timeEncodeRd1 += (end - begin);
    }

    public void solveRd1(boolean timedScript) {
        long begin = System.currentTimeMillis();
        try {
            String command = "/bin/bash";
            String scriptPath = timedScript ? "./runTimedMaxSAT.sh" : "./runMaxSAT.sh";

            // Create a ProcessBuilder with the specified command
            ProcessBuilder processBuilder = new ProcessBuilder(command, scriptPath);
            processBuilder.directory(new File(System.getProperty("user.dir")
                    + "/" + maxsatFilesPath));

            // Start the process
            Process process = processBuilder.start();

            // Wait for the process to finish
            int exitCode = process.waitFor();
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
        long end = System.currentTimeMillis();
        this.timeSolveRd1 += (end - begin);
    }

    public void encodeRd2() throws IOException {
        long begin = System.currentTimeMillis();

        List<Integer> maxSATSol = readMaxSATSol(maxsatFilesPath + "sol.txt");
        if (!maxSATSol.isEmpty()) {
            String maxSATInputRd2 = this.mse.encodeSATRd2(maxSATSol);
            writeTo(maxSATInputRd2, maxsatFilesPath + "maxsat2Input.txt");
        }

        long end = System.currentTimeMillis();
        this.timeEncodeRd2 += (end - begin);
    }

    public void solveRd2(boolean timedScript) {
        long begin = System.currentTimeMillis();

        try {
            String command = "/bin/bash";
            String scriptPath = timedScript ? "./runTimedMaxSAT2.sh" : "./runMaxSAT2.sh";

            // Create a ProcessBuilder with the specified command
            ProcessBuilder processBuilder = new ProcessBuilder(command, scriptPath);
            processBuilder.directory(new File(System.getProperty("user.dir")
                    + "/" + maxsatFilesPath));

            // Start the process
            Process process = processBuilder.start();

            // Wait for the process to finish
            int exitCode = process.waitFor();
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }

        long end = System.currentTimeMillis();
        this.timeSolveRd2 += (end - begin);
    }

    public List<CoqProof> decodeScript() throws IOException {
        // Convert sol to tactics
        long begin = System.currentTimeMillis();
        List<Integer> maxSATSol = readMaxSATSol(maxsatFilesPath + "sol2.txt");
        List<CoqProof> resScript = new ArrayList<>();
        if (!maxSATSol.isEmpty()) {
            // todo: add stuff here to ensure 2nd round unsat in accounted for too
            resScript = mse.maxSATSolToTactics(maxSATSol, this.config);
        }
//        for (CoqProof pg: mse.pgraphs) {
//            visualize(pg.pgraph, this.config);
//        }
        long end = System.currentTimeMillis();
        this.timeDecodeToScript += (end - begin);

        return resScript;
    }

    public ProofGraph decodeGraph() {
        // Convert sol to graph
        long begin = System.currentTimeMillis();
        List<Integer> maxSATSol = readMaxSATSol(maxsatFilesPath + "sol2.txt");
        ProofGraph res = null;
        if (!maxSATSol.isEmpty()) {
            res = mse.maxSATSolToGraph(maxSATSol, true);
        }
        long end = System.currentTimeMillis();
        this.timeDecodeToGraph += (end - begin);
        return res;
    }



    // Read in a solution file
    public List<Integer> readMaxSATSol(String file) {
        List<Integer> maxSATSol = MaxSATUtil.getSolutionList(file);

        if (maxSATSol == null) return new ArrayList<>();
        maxSATSol = maxSATSol.stream().filter(x -> x > 0).collect(Collectors.toList());
        if (maxSATSol.stream().filter(s -> s <= this.mse.vCount).collect(Collectors.toList()).isEmpty()) return new ArrayList<>();

        return maxSATSol;
    }

    // Display a proof graph
    public static void visualize(ProofGraph pg, BmConfig config) {
        if (config.visualizeGraphs) GraphVisualizer.visualize(pg);
    }

    // Evaluate compression of resulting tactics. Returns [originalLen, contractedLen, contractionRate]
    public Map<String, String> evaluate(int groupID, List<Integer> proofIDs, String filename, boolean timeoutP, boolean unsatP, int timeoutInSeconds) throws Exception {
        // run-id | input-proof-1-id | input-proof-2-id | finished? | run-time |  tactic-len | tactic-args | tactic-valid | compressed-proof-valid | compression-rate
        CompressionEval ce = new CompressionEval(mse);
        // update fields: timeout? unsat? run-time
        Map<String, String> evalResult = new HashMap<>();
        evalResult.put("timeout?", Boolean.toString(timeoutP));
        evalResult.put("unsat?", Boolean.toString(unsatP));
        evalResult.put("runtime (s)", String.valueOf(timeoutP ? timeoutInSeconds : (this.totalTime / 1000)));
        evalResult.put("proof-IDs", proofIDs.toString());


        // update fields: tactic num, tactic #i len, tactic #i num args, tactic #i valid
        ce.updateCustomTacticsData(evalResult);

        // update fields: input proof #i ID, input proof #i raw-len:compressed-len, total compression rate
        this.originalScriptList = CompressionEval.getRawProofScriptList(proofIDs, filename);

//        System.out.println(findLongestCommonTactics(originalScriptList.get(0), originalScriptList.get(1)));
        // System.out.println(findBaselineSyntacticTactics(proofIDs, this.filename));
        List<String> contractedProofs = (timeoutP || unsatP || mse.connCompMcsIDs.isEmpty()) ? new ArrayList<>(this.originalScriptList) : ce.graphsToScripts();
        // write to resources
        this.contractedScriptList = contractedProofs;
        // System.out.println("proof ids: " + proofIDs + " --------------------------");

        // todo: delete later maybe, just here to check correctness
        if (!timeoutP && !unsatP && !mse.connCompMcsIDs.isEmpty()) {
            try {
                String rawContent = Files.readString(Paths.get(filename));
                String start = "Inductive t : Type := Nil | Cons (lo hi: Z) (tl: t).";
                rawContent = rawContent.replace(start,
                        start + "\n" + this.mcsScript + "\n");
                for (int i = 0; i < this.originalScriptList.size(); i++) {
                    String rawProof = this.originalScriptList.get(i);
                    String contractedProof = this.contractedScriptList.get(i);
                    contractedProof = contractedProof.contains("Proof.") ?
                            contractedProof.substring(contractedProof.indexOf("Proof."), contractedProof.indexOf("Qed") + 4) :
                            contractedProof.substring(contractedProof.indexOf("Next Obligation."), contractedProof.indexOf("Qed") + 4);
                    rawContent = rawContent.replace(rawProof, contractedProof);
                }
                writeTo(rawContent, compressionEvalPath + "replaced-files/s" + groupID + ".v");
            } catch (IOException e) {
                System.err.println("Error reading file: " + e.getMessage());
            }
        }

        ce.updateCompressionData(this.originalScriptList, this.contractedScriptList, evalResult);
        // compare the length
//        if (isContractedProofValid(contractedProofs, filename, proofIDs))
//            return CompressionEval.getContractionData(this.originalScriptList, this.contractedScriptList);
//        else
//            return new ArrayList<>();
        return evalResult;
    }



    public boolean runWithTimeout(int timeoutInSeconds) {
        boolean timeout = false;
        ExecutorService executor = Executors.newSingleThreadExecutor();
        Future<Void> future = executor.submit(() -> {
            run();
            return null;
        });

        try {
            future.get(timeoutInSeconds, TimeUnit.SECONDS);
        } catch (TimeoutException e) {
            // Handle timeout
            timeout = true;
            System.out.println("Function call timed out after" + timeoutInSeconds + " seconds.");
        } catch (InterruptedException | ExecutionException e) {
            // Handle other exceptions
            e.printStackTrace();
        } finally {
            future.cancel(true); // Cancel the task if it's still running
            executor.shutdown();
        }
        return timeout;
    }

    public void run() throws IOException {
        this.encodeRd1();
        this.solveRd1(false);
        this.encodeRd2();
        this.solveRd2(false);
        this.mcsScript = decodeScript();

        this.totalTime = this.timeConvert + this.timeEncodeRd1 + this.timeSolveRd1 + this.timeEncodeRd2 +
                this.timeEncodeRd2 + this.timeDecodeToScript;
//        System.out.println("custom tactics: \n" + this.mcsScript);
    }

    public Set<CoqProof> runAllCommonSubgraphs(int timeoutInSeconds) throws IOException {
        // while not unsat, keep going
        boolean unsatP = false;
        boolean timeoutP = false;

        List<List<Integer>> solutionBans = new ArrayList<>();
        Set<String> commonTacsStr = new HashSet<>();
        Set<String> solutions2 = new HashSet<>();
        Set<CoqProof> commonTacs = new HashSet<>();
        int i = 0;
        long cumulativeTime = 0;
        while (!unsatP) {
            this.mse = new MaxSatEncoder(this.lemmas);
            if (cumulativeTime / 1000.0 >= timeoutInSeconds) {
                timeoutP = true;
                break;
            }
            long start = System.currentTimeMillis();
            String maxSATInput = this.mse.encodeSATAllCommonGraphs(false, solutionBans);
            writeTo(maxSATInput, maxsatFilesPath + "maxsatInput.txt");
            writeTo("", maxsatFilesPath + "sol.txt");
            this.solveRd1(true);

            this.encodeRd2();
            writeTo("", maxsatFilesPath + "sol2.txt");
            this.solveRd2(true);

            List<Integer> currSol = readMaxSATSol(maxsatFilesPath + "sol.txt");
            if (i % 1000 == 0) {
//                System.out.println("found solution at round " + i);
//                System.out.println("found solution2 at round " + (i++));
//                System.out.println("curr Sol: " + currSol);
            }
            unsatP = currSol.isEmpty();
            solutionBans.add(this.mse.getFreeVarAssgned(maxsatFilesPath + "sol.txt").stream().map(x -> -x).collect(Collectors.toList()));

            List<Integer> finalSol = readMaxSATSol(maxsatFilesPath + "sol2.txt");
            if (solutions2.contains(finalSol.toString())) continue;
            solutions2.add(finalSol.toString());

            if (finalSol != null && !finalSol.isEmpty()) {
                commonTacs.addAll(mse.maxSATSolToTactics(finalSol, this.config));
            }

//            if (!currSol.isEmpty()) {
//                // todo: add stuff here to ensure 2nd round unsat in accounted for too
//                for (CoqProof t: mse.maxSATSolToTactics(currSol, this.config)) {
//                    if (!commonTacsStr.contains(t.raw_string)) {
//                        commonTacsStr.add(t.raw_string);
//                        commonTacs.add(t);
//                    }
//                }
//            }

            long end = System.currentTimeMillis();
            cumulativeTime += (end - start);
            System.out.println("cumulative time: " + cumulativeTime);
        }
        System.out.println("solution bans: " + solutionBans);
        System.out.println("finished extracting");

        if (timeoutP) System.out.println("Input TLE'd");
        return commonTacs;
    }

}
