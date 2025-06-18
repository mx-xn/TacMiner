package test.main;

import main.Engine;
import main.Main.*;
import main.config.*;
import main.encode.*;
import main.eval.*;
import main.lib_assembler.LibAssembler;
import main.proofgraph.*;
import main.sampler.*;

import java.io.IOException;
import java.util.*;
import org.junit.Test;
import static org.junit.jupiter.api.Assertions.*;

/*
 * Tests for the overall algorithm. This treats the MaxSAT subroutine as a black-box. For MaxSAT-specific tests, see other files.
 */
public class MainTest {
//    static final int selectedConfig = 1;
//    static final Config[] configs = {
//        new Config(1, 2, 90, Paths.coqFilesPath + "SimpleAlgebra2.json", Paths.coqFilesPath + "SimpleAlgebra2.v", Paths.compressionEvalPath + "SimpleAlgebra2_compressed.v", false),
//        new Config(1, 2, 90, Paths.coqFilesPath + "IntvSets.json", Paths.coqFilesPath + "IntvSets.v", Paths.compressionEvalPath + "IntvSets_compressed.v", false)
//    };

    // Run the entire pipeline on a simple example
//    public static void main(String[] args) throws IOException {
//        Config selected = configs[selectedConfig];
//        selected.visualizeGraphs = false;
////        LibAssembler.Library library = main.Main.run(selected, ExtractType.MAXSAT);
//
////        System.out.println(library);
////        System.out.println(library.printDiagnostics());
//    }
//
//    @Test
//    public void testReadProofs() {
//        // .json --> CoqProof conversion
//        Config selected = configs[selectedConfig];
//        List<CoqProof> proofs = Encoder.inputCoqScripts(selected.inputJSON);
//
//        assertEquals(proofs.size(), 4);
//        assertEquals(proofs.get(0).lemma_name, "algb_nat_zero");
//        assertEquals(proofs.get(1).lemma_name, "algb_identity_sum");
//        assertEquals(proofs.get(2).lemma_name, "algb_identity_sum2");
//        assertEquals(proofs.get(3).lemma_name, "algb_identity_sum3");
//
//        assertEquals(proofs.get(0).tactics.get(0).signature, "intros _o .");
//        assertEquals(proofs.get(0).tactics.get(1).signature, "induction _i .");
//        assertEquals(proofs.get(0).tactics.get(2).signature, "simpl .");
//        assertEquals(proofs.get(0).tactics.size(), 7);
//    }
//
//    @Test
//    public void testSampler() {
//        // sampler gives the appropriate number of samples, in the desired order
//        Config selected = configs[selectedConfig];
//        List<CoqProof> proofs = Encoder.inputCoqScripts(selected.inputJSON);
//
//        List<List<CoqProof>> samplesNone = Sampler.getSamples(proofs, Sampler.SamplingType.NONE);
//        assertEquals(samplesNone.size(), 6);
//
//        List<List<CoqProof>> samplesCosine = Sampler.getSamples(proofs, Sampler.SamplingType.COSINE);
//        assertEquals(samplesCosine.size(), 6);
//
//        for(List<CoqProof> pair : samplesCosine) {
//            assertEquals(pair.size(), 2);
//        }
//    }
//
//    @Test
//    public void testTacticExtraction() {
//        // MaxSAT subroutine works as expected (as a black box)
//        Config selected = configs[selectedConfig];
//        selected.visualizeGraphs = false;
//        List<CoqProof> proofs = Encoder.inputCoqScripts(selected.inputJSON);
//
//        List<CoqProof> tacs1 = main.Main.extractTactics(Arrays.asList(proofs.get(0), proofs.get(1)), selected);
//        List<CoqProof> tacs2 = main.Main.extractTactics(Arrays.asList(proofs.get(1), proofs.get(2)), selected);
//        List<CoqProof> tacs3 = main.Main.extractTactics(Arrays.asList(proofs.get(2), proofs.get(3)), selected);
//
//        assertEquals(tacs1.size(), 0);
//        assertEquals(tacs2.size(), 1);
//        assertEquals(tacs3.size(), 1);
//
//        assertEquals(tacs2.get(0).tactics.size(), 3);
//        assertEquals(tacs3.get(0).tactics.size(), 3);
//    }
//
//    @Test
//    public void testProofGraphGen() {
//        // CoqProof --> ProofGraph conversion
//        Config selected = configs[selectedConfig];
//        selected.visualizeGraphs = false;
//        List<CoqProof> proofs = Encoder.inputCoqScripts(selected.inputJSON);
//        List<CoqProof> customTacs = main.Main.extractTactics(Arrays.asList(proofs.get(2), proofs.get(1)), selected);
//
//        Encoder.initPGs(customTacs);
//        assertEquals(customTacs.get(0).pgraph.vertices.size(), 3);
//        // Engine.visualize(customTacs.get(0).pgraph, new Config());
//    }
//
//    @Test
//    public void testSubgraphDetection() {
//        // subgraph isomorphism detection
//        Config selected = configs[selectedConfig];
//        selected.visualizeGraphs = false;
//        List<CoqProof> proofs = Encoder.inputCoqScripts(selected.inputJSON);
//        List<CoqProof> customTacs = main.Main.extractTactics(Arrays.asList(proofs.get(2), proofs.get(1)), selected);
//
//        Encoder.initPGs(proofs);
//        Encoder.initPGs(customTacs);
//
//        List<Integer> match = CompressionEval.searchSubgraph(proofs.get(1).pgraph, customTacs.get(0).pgraph, new ArrayList<>(), new HashSet<>());
//        assertEquals(match, Arrays.asList(0, 1, -1, 2));
//
//        match = CompressionEval.searchSubgraph(proofs.get(2).pgraph, customTacs.get(0).pgraph, new ArrayList<>(), new HashSet<>());
//        assertEquals(match, Arrays.asList(0, 1, -1, -1, 2));
//
//        match = CompressionEval.searchSubgraph(proofs.get(3).pgraph, customTacs.get(0).pgraph, new ArrayList<>(), new HashSet<>());
//        assertEquals(match, Arrays.asList(0, 1, -1, -1, 2));
//
//        match = CompressionEval.searchSubgraph(proofs.get(0).pgraph, customTacs.get(0).pgraph, new ArrayList<>(), new HashSet<>());
//        assertEquals(match, null);
//    }

    @Test
    public void testTacticConstruction() {
        // given an embedding of a custom tactic, build a single CoqTactic object out of it
//        Config selected = configs[selectedConfig];
//        selected.visualizeGraphs = false;
//        List<CoqProof> proofs = Encoder.inputCoqScripts(selected.inputJSON);
//        List<CoqProof> customTacs = main.Main.extractTactics(Arrays.asList(proofs.get(2), proofs.get(1)), selected);
//
//        Encoder.initPGs(proofs);
//        Encoder.initPGs(customTacs);
//
//        List<Integer> match = CompressionEval.searchSubgraph(proofs.get(1).pgraph, customTacs.get(0).pgraph, new ArrayList<>(), new HashSet<>());
//        CoqTactic custom = CompressionEval.populateCustom(proofs.get(1), customTacs.get(0), match);
//
//        assertTrue(custom.signature.startsWith("custom"));
//        assertEquals(custom.signature, custom.sig_no_out_arg); // This may not be true
//
//        assertEquals(custom.inputs.size(), 1);
//        assertEquals(custom.outputs.size(), 4);
//        assertEquals(custom.args.size(), 2);
//        assertTrue(custom.args.contains("a") && custom.args.contains("H"));
    }

    @Test
    public void testCompression() {
        // Full compression pipeline: compress a proof given a tactic
//        Config selected = configs[selectedConfig];
//        selected.visualizeGraphs = false;
//        List<CoqProof> proofs = Encoder.inputCoqScripts(selected.inputJSON);
//        List<CoqProof> customTacs = main.Main.extractTactics(Arrays.asList(proofs.get(2), proofs.get(1)), selected);
//
//        Encoder.initPGs(proofs);
//        Encoder.initPGs(customTacs);
//
//        CoqProof compressed = CompressionEval.compressProof(proofs.get(1), customTacs.get(0));
//
//        assertEquals(compressed.lemma_name, "algb_identity_sum");
//        assertEquals(compressed.type, CoqProof.SequenceType.PROOF);
//        assertEquals(compressed.raw_string, null);
//        assertEquals(compressed.tactics.size(), 2);
//        assertEquals(compressed.tactics.get(0).id, 0);
//        assertEquals(compressed.tactics.get(1).id, 1);
//        assertTrue(compressed.tactics.get(1).signature.startsWith("custom"));
//
//        assertEquals(compressed.tactics, compressed.pgraph.vertices);
//        assertEquals(compressed.pgraph.adjList, Arrays.asList(Arrays.asList(), Arrays.asList(new ProofGraph.Edge(1, 0, 1, 0))));
//
//        compressed = CompressionEval.compressProof(proofs.get(2), customTacs.get(0));
//
//        assertEquals(compressed.lemma_name, "algb_identity_sum2");
//        assertEquals(compressed.tactics.size(), 3);
//        assertTrue(compressed.tactics.get(2).signature.startsWith("custom"));
//
//        assertEquals(compressed.pgraph.adjList, Arrays.asList(Arrays.asList(new ProofGraph.Edge(0, 1, 0, 0)), Arrays.asList(), Arrays.asList(new ProofGraph.Edge(2, 0, 1, 0))));
//
//        // No compression case
//        compressed = CompressionEval.compressProof(proofs.get(0), customTacs.get(0));
//        assertEquals(compressed, proofs.get(0));
//        assertEquals(compressed.pgraph, proofs.get(0).pgraph);
    }

    @Test
    public void testPart1() {
        // Part 1: Candidate Tactic Extraction
//        Config config = configs[selectedConfig];
//        config.visualizeGraphs = false;
//        List<CoqProof> proofs = Encoder.inputCoqScripts(config.inputJSON);
//        List<List<CoqProof>> samplesCosine = Sampler.getSamples(proofs, Sampler.SamplingType.COSINE);
//        Set<CoqProof> candidateTactics = new HashSet<>();
//        for(List<CoqProof> pair : samplesCosine) {
//            candidateTactics.addAll(main.Main.extractTactics(pair, config));
//        }
//        Encoder.initPGs(candidateTactics);
//        int tacID = 0;
//        for(CoqProof candidate : candidateTactics) {
//            candidate.lemma_name = "custom" + tacID++;
//        }
//
//        assertEquals(candidateTactics.size(), 2);
    }

    @Test
    public void testFullPipeline() throws IOException {
        // Test full pipeline, mostly by confirming compression values
//        Config selected = configs[selectedConfig];
//        selected.visualizeGraphs = false;
//        LibAssembler.Library library = main.Main.run(selected, ExtractType.MAXSAT);
//
//        assertEquals(library.getCorpusSize(), 21);
//        assertEquals(library.getCompressedSize(), 15);
//        assertEquals(library.getLibrarySize(), 3);
//        assertEquals(library.getOverallSize(), 18);
//        assertEquals(library.getCompression(), (double) 21 / 18);
    }
}
