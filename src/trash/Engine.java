package trash;

import main.config.BmConfig;
import main.encode.*;
import main.eval.CompressionEval;
import main.proofgraph.*;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.stream.Collectors;

import static main.config.Path.*;

public class Engine {
    public String filename;
    List<CoqProof> lemmas;
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

    // Display a proof graph
    public static void visualize(ProofGraph pg, BmConfig config) {
        if (config.visualizeGraphs) GraphVisualizer.visualize(pg);
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

}
