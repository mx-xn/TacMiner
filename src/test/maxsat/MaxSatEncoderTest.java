// package test.maxsat;

// import main.config.Paths;
// import main.encode.*;
// import main.maxsat.MaxSatEncoder;
// import main.proofgraph.ProofGraph;
// import resources.TempTestInput;
// import org.junit.Test;

// import java.util.*;

// import static main.maxsat.MaxSATUtil.*;
// import static org.junit.jupiter.api.Assertions.*;

// // TODO: old comprehensive tests are outdated

// public class MaxSatEncoderTest {
//     MaxSatEncoder maxSatEnc;

//     public void initMAXSATEncoder(List<List<CoqTactic>> proofs) {
//         List<ProofGraph> pgs = Encoder.getPGs(proofs);
//         this.maxSatEnc = new MaxSatEncoder(pgs);
//     }

//     @Test
//     public void testMetadata() {
//         initMAXSATEncoder(Encoder.inputCoqScripts(Paths.coqFilesPath + "SimpleAlgebra.json"));
//         List<ProofGraph.Edge> meta = maxSatEnc.getMetadata();
//         assertTrue(meta.contains(new ProofGraph.Edge(-1, -1, 0, 0)));
//         assertTrue(meta.contains(new ProofGraph.Edge(-1, -1, 1, 1)));
//         assertTrue(meta.contains(new ProofGraph.Edge(-1, -1, 1, 0)));
//         assertTrue(meta.contains(new ProofGraph.Edge(-1, -1, 2, 1)));
//         assertEquals(meta.size(), 4);
//     }

//     @Test
//     public void testVertexMap() {
//         initMAXSATEncoder(Encoder.inputCoqScripts(Paths.coqFilesPath + "SimpleAlgebra.json"));
//         List<String> tacTypes = maxSatEnc.initVertexTypeMap();
//         assertTrue(tacTypes.contains("intros ."));
//         assertTrue(tacTypes.contains("induction _ ."));
//         assertTrue(tacTypes.contains("simpl ."));
//         assertTrue(tacTypes.contains("reflexivity ."));
//         assertTrue(tacTypes.contains("rewrite _ ."));
//         assertTrue(tacTypes.contains("destruct ( _ ) eqn : _o ."));
//         assertEquals(tacTypes.size(), 6);
//     }

// //    @Test
// //    public void testVarCount() {
// //        initMAXSATEncoder(Encoder.inputCoqScripts(Paths.coqFilesPath + "SimpleAlgebra.json"));
// //        assertEquals(maxSatEnc.countDomainIndicator(), 3 * 11);
// //        assertEquals(maxSatEnc.countTypeIndicator(), 6 * (3 + 11));
// //        assertEquals(maxSatEnc.countCFlow(), 3 * 3 + 7 * 7 + 4 * 4);
// //    }

//     @Test
//     public void testVarMaps() {
//         initMAXSATEncoder(Encoder.inputCoqScripts(Paths.coqFilesPath + "SimpleAlgebra.json"));
//         int[][][] domainVars = maxSatEnc.computeDomainVars();
//         int min = Integer.MAX_VALUE, max = 0;
//         for (int[][] e1: domainVars) {
//             for (int[] e2: e1) {
//                 for (int e3: e2) {
//                     if (e3 != 0) {
//                         min = Math.min(min, e3);
//                         max = Math.max(max, e3);
//                     }
//                 }
//             }
//         }
//         assertEquals(min, 3 + 1);
//         assertEquals(max, 3 * 11 + 3);

//         int[][][] typeVars = maxSatEnc.computeTypeVars();
//         min = Integer.MAX_VALUE; max = 0;
//         for (int[][] e1: typeVars) {
//             for (int[] e2: e1) {
//                 for (int e3: e2) {
//                     if (e3 != 0) {
//                         min = Math.min(min, e3);
//                         max = Math.max(max, e3);
//                     }
//                 }
//             }
//         }
//         assertEquals(min, 3 * 11 + 3 + 1);
//         assertEquals(max, 3 * 11 + 3 + 6 * (3 + 11));

//         int[][][] cfVars = maxSatEnc.computeCFVars();
//         min = Integer.MAX_VALUE; max = 0;
//         for (int[][] e1: cfVars) {
//             for (int[] e2: e1) {
//                 for (int e3: e2) {
//                     if (e3 != 0) {
//                         min = Math.min(min, e3);
//                         max = Math.max(max, e3);
//                     }
//                 }
//             }
//         }
//         assertEquals(min, 3 * 11 + 3 + 6 * (3 + 11) + 1);
//         assertEquals(max, 3 * 11 + 3 + 6 * (3 + 11) + 3 * 3 + 7 * 7 + 4 * 4);

//         assertEquals(maxSatEnc.printStat(), "Stats ------------------------------\n" + //
//         "num tactics: 6\nnum graphs: 2\nnum candidates: 3\nnum min input nodes: 4\nnum max input nodes: 7\n" + //
//         "End Stats ------------------------------\n");
//     }

    



//     // public void initMAXSATEncoder(List<CoqTactic> tacL1, List<CoqTactic> tacL2) {
//     //     Encoder enc1 = new Encoder(tacL1);
//     //     Encoder enc2 = new Encoder(tacL2);
//     //     ProofGraph pg1 = enc1.generateGraph();
//     //     ProofGraph pg2 = enc2.generateGraph();
//     //     this.maxSatEnc = new MaxSatEncoder(Arrays.asList(pg1, pg2));
//     // }

// //     @Test
// //     public void testMaxSATOutput() {
// //         // todo: there must exist an edge! a bunch of disconnected vertices are bad
// //         // numTypes = 7
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         System.out.println(this.maxSatEnc.encodeSAT(true));
// //     }

// //     @Test
// //     public void testComputeDomainVars() {
// //         initMAXSATEncoder(TempTestInput.l1, TempTestInput.l2);
// //         // v = 5, g = 2, w max = 8

// //         // var starting from 4
// //         int[][][] expected = {
// //                 {{6, 7, 8, 9, 10, 11, 0, 0}, {12, 13, 14, 15, 16, 17, 18, 19}},
// //                 {{20, 21, 22, 23, 24, 25, 0, 0}, {26, 27, 28, 29, 30, 31, 32, 33}},
// //                 {{34, 35, 36, 37, 38, 39, 0, 0}, {40, 41, 42, 43, 44, 45, 46, 47}},
// //                 {{48, 49, 50, 51, 52, 53, 0, 0}, {54, 55, 56, 57, 58, 59, 60, 61}},
// //                 {{62, 63, 64, 65, 66, 67, 0, 0}, {68, 69, 70, 71, 72, 73, 74, 75}}
// //         };

// //         int[][][] actual = this.maxSatEnc.computeDomainVars();
// //         assertArrayEquals(expected, actual);


// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // v = 2, g = 2, w max = 3
// //         expected = new int[][][]{
// //                 {{3, 4, 5}, {6, 7, 8}},
// //                 {{9, 10, 11}, {12, 13, 14}}
// //         };
// //         actual = this.maxSatEnc.computeDomainVars();
// //         assertArrayEquals(expected, actual);
// //     }


// //     @Test
// //     public void testComputeTypeVars() {
// //         // numTypes = 7
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // vCount = 2, vDomainCount = 12
// //         // t = 7, g + 1 = 2 + 1, w max = 3

// //         // var starting from 4
// //         int[][][] expected = {
// //                 {{15, 16, 0}, {17, 18, 19}, {20, 21, 22}},
// //                 {{23, 24, 0}, {25, 26, 27}, {28, 29, 30}},
// //                 {{31, 32, 0}, {33, 34, 35}, {36, 37, 38}},
// //                 {{39, 40, 0}, {41, 42, 43}, {44, 45, 46}},
// //                 {{47, 48, 0}, {49, 50, 51}, {52, 53, 54}},
// //                 {{55, 56, 0}, {57, 58, 59}, {60, 61, 62}},
// //                 {{63, 64, 0}, {65, 66, 67}, {68, 69, 70}}
// //         };

// //         int[][][] actual = this.maxSatEnc.computeTypeVars();
// //         assertArrayEquals(expected, actual);
// //     }

// //     @Test
// //     public void testComputeCFVars() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // vCount = 2, vDomainCount = 12
// //         // vTypeCount = 7 * 6 + 7 * 2 = 56
// //         // g + 1 = 2 + 1, w-max = 3, w-max = 3

// //         // var starting from 71
// //         int[][][] expected = {
// //                 {{71, 72, 0}, {73, 74, 0}, {0, 0, 0}},
// //                 {{75, 76, 77}, {78, 79, 80}, {81, 82, 83}},
// //                 {{84, 85, 86}, {87, 88, 89}, {90, 91, 92}},
// //         };

// //         int[][][] actual = this.maxSatEnc.computeCFVars();
// //         assertArrayEquals(expected, actual);
// //     }

// //     @Test
// //     public void testConstantTypeInd() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // vCount = 2, vDomainCount = 12
// //         // vTypeCount = 7 * 6 + 7 * 2 = 56 (15 - 70)
// //         // g + 1 = 2 + 1, w-max = 3, w-max = 3

// //         // var starting from 71
// //         List<Integer> expected = Arrays.asList(
// //                 17, -18, -19, -20, -21, -22,
// //                 -25, 26, -27, -28, -29, 30,
// //                 -33, -34, -35, -36, -37, -38,
// //                 -41, -42, -43, 44, -45, -46,
// //                 -49, -50, 51, -52, 53, -54,
// //                 -57, -58, -59, -60, -61, -62,
// //                 -65, -66, -67, -68, -69, -70
// //         );

// //         List<Integer> actual = this.maxSatEnc.constantTypeInd();
// //         assertEquals(expected, actual);
// //     }

// //     // 3 * (4 + 9 + 9) = 66
// //     @Test
// //     public void testConstantCFInd() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // [[1, 0], [0, 0], [1, 1]]
// //         // vCount = 2, vDomainCount = 12
// //         // 71 - 136
// //         // g + 1 = 2 + 1, w-max = 3, w-max = 3

// //         // G1: (1, 0, 1), (2, 0, 1), (1, 1, 2) [(m, v1, v2)]
// //         // G2: (1, 0, 1), (0, 0, 2)

// //         // var starting from 71
// //         List<Integer> expected = Arrays.asList(
// //                 // M1
// //                 -75, -76, -77, -78, -79, -80, -81, -82, -83,
// //                 -84, -85, 86, -87, -88, -89, -90, -91, -92,

// //                 -97, 98, -99, -100, -101, 102, -103, -104, -105,
// //                 -106, 107, -108, -109, -110, -111, -112, -113, -114,

// //                 -119, 120, -121, -122, -123, -124, -125, -126, -127,
// //                 -128, -129, -130, -131, -132, -133, -134, -135, -136
// //         );

// //         List<Integer> actual = this.maxSatEnc.constantCFInd();
// //         assertEquals(expected, actual);
// //     }

// // //    @Test
// // //    public void testDomainConstraintPermute() {
// // //        initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// // //        // v = 2, g = 2, w max = 3
// // ////        {{3, 4, 5}, {6, 7, 8}},
// // ////        {{9, 10, 11}, {12, 13, 14}}
// // //        int[][][] domainVars = this.maxSatEnc.computeDomainVars();
// // //        List<List<Integer>> actual = this.maxSatEnc.domainConstraintPermute(0, domainVars);
// // //
// // //        List<List<Integer>> expected = Arrays.asList(
// // //                Arrays.asList(3, 6),
// // //                Arrays.asList(4, 6),
// // //                Arrays.asList(5, 6),
// // //
// // //                Arrays.asList(3, 7),
// // //                Arrays.asList(4, 7),
// // //                Arrays.asList(5, 7),
// // //
// // //                Arrays.asList(3, 8),
// // //                Arrays.asList(4, 8),
// // //                Arrays.asList(5, 8)
// // //        );
// // //        assertEquals(expected, actual);
// // //
// // //        actual = this.maxSatEnc.domainConstraintPermute(1, domainVars);
// // //        expected = Arrays.asList(
// // //                Arrays.asList(9, 12),
// // //                Arrays.asList(10, 12),
// // //                Arrays.asList(11, 12),
// // //
// // //                Arrays.asList(9, 13),
// // //                Arrays.asList(10, 13),
// // //                Arrays.asList(11, 13),
// // //
// // //                Arrays.asList(9, 14),
// // //                Arrays.asList(10, 14),
// // //                Arrays.asList(11, 14)
// // //        );
// // //        assertEquals(expected, actual);
// // //    }

// //     @Test
// //     public void testDomainConstraint() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // v = 2, g = 2, w max = 3
// // //        {{3, 4, 5}, {6, 7, 8}},
// // //        {{9, 10, 11}, {12, 13, 14}}

// //         List<List<Integer>> actual = domainConstraint(this.maxSatEnc);
// //         List<List<Integer>> expected = Arrays.asList(
// //                 Arrays.asList(-3, -6, 1), Arrays.asList(-4, -6, 1), Arrays.asList(-5, -6, 1),
// //                 Arrays.asList(-3, -7, 1), Arrays.asList(-4, -7, 1), Arrays.asList(-5, -7, 1),
// //                 Arrays.asList(-3, -8, 1), Arrays.asList(-4, -8, 1), Arrays.asList(-5, -8, 1),

// //                 Arrays.asList(-9, -12, 2), Arrays.asList(-10, -12, 2), Arrays.asList(-11, -12, 2),
// //                 Arrays.asList(-9, -13, 2), Arrays.asList(-10, -13, 2), Arrays.asList(-11, -13, 2),
// //                 Arrays.asList(-9, -14, 2), Arrays.asList(-10, -14, 2), Arrays.asList(-11, -14, 2),

// //                 Arrays.asList(3, 4, 5, -1), Arrays.asList(6, 7, 8, -1),
// //                 Arrays.asList(9, 10, 11, -2), Arrays.asList(12, 13, 14, -2)
// //         );
// //         // 3 6 1; 4 6 1; 5 6 1;
// //         // 3 7 1; 4 7 1; 5 7 1;
// //         // 3 8 1; 4 8 1; 5 8 1;

// //         // 9 12 2; 10 12 2; 11 12 2;
// //         // 9 13 2; 10 13 2; 11 13 2;
// //         // 9 14 2; 10 14 2; 11 14 2;

// //         // 3 4 5 -1; 6 7 8 -1;
// //         // 9 10 11 -2; 12 13 14 -2;
// //         assertEquals(expected, actual);
// //     }

// //     @Test
// //     public void testOntoConstraint() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // v = 2, g = 2, w max = 3
// // //        {{3, 4, 5}, {6, 7, 8}},
// // //        {{9, 10, 11}, {12, 13, 14}}

// //         List<List<Integer>> actual = ontoConstraint(this.maxSatEnc);
// //         List<List<Integer>> expected = Arrays.asList(
// //                 Arrays.asList(-3, -4), Arrays.asList(-3, -5), Arrays.asList(-4, -5),
// //                 Arrays.asList(-6, -7), Arrays.asList(-6, -8), Arrays.asList(-7, -8),
// //                 Arrays.asList(-9, -10), Arrays.asList(-9, -11), Arrays.asList(-10, -11),
// //                 Arrays.asList(-12, -13), Arrays.asList(-12, -14), Arrays.asList(-13, -14)
// //         );
// //         assertEquals(expected, actual);
// //     }

// //     @Test
// //     public void testOneToOneConstraint() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // v = 2, g = 2, w max = 3
// //         // domainVars
// // //        {{3, 4, 5}, {6, 7, 8}},
// // //        {{9, 10, 11}, {12, 13, 14}}

// //         List<List<Integer>> actual = oneToOneConstraint(this.maxSatEnc);
// //         List<List<Integer>> expected = Arrays.asList(
// //                 Arrays.asList(-3, -9), Arrays.asList(-4, -10), Arrays.asList(-5, -11),
// //                 Arrays.asList(-6, -12), Arrays.asList(-7, -13), Arrays.asList(-8, -14)
// //         );
// //         assertEquals(expected, actual);
// //     }

// //     @Test
// //     public void testNoSpurCFConstraint() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // v = 2, #meta = 3; vCFCount = 4 + 9 + 9 = 22 71 + 22 = 93
// //         // CFVars
// // //        {{71, 72, 0}, {73, 74, 0}, {0, 0, 0}},
// // //        {{75, 76, 77}, {78, 79, 80}, {81, 82, 83}},
// // //        {{84, 85, 86}, {87, 88, 89}, {90, 91, 92}},

// //         List<List<Integer>> actual = noSpurCFConstraint(this.maxSatEnc);
// //         List<List<Integer>> expected = Arrays.asList(
// //                 Arrays.asList(-71, 1),
// //                 Arrays.asList(-72, 1), Arrays.asList(-72, 2),
// //                 Arrays.asList(-73, 2), Arrays.asList(-73, 1),
// //                 Arrays.asList(-74, 2),
// //                 Arrays.asList(-93, 1),
// //                 Arrays.asList(-94, 1), Arrays.asList(-94, 2),
// //                 Arrays.asList(-95, 2), Arrays.asList(-95, 1),
// //                 Arrays.asList(-96, 2),
// //                 Arrays.asList(-115, 1),
// //                 Arrays.asList(-116, 1), Arrays.asList(-116, 2),
// //                 Arrays.asList(-117, 2), Arrays.asList(-117, 1),
// //                 Arrays.asList(-118, 2)
// //         );
// //         assertEquals(expected, actual);
// //     }


// //     @Test
// //     public void testTypePreserveConstraint() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // v = 2, g = 2, w max = 3
// //         // domainVars
// // //        {{3, 4, 5}, {6, 7, 8}},
// // //        {{9, 10, 11}, {12, 13, 14}}
// //         // typeVars
// // //        {{15, 16, 0}, {17, 18, 19}, {20, 21, 22}},
// // //        {{23, 24, 0}, {25, 26, 27}, {28, 29, 30}},
// // //        {{31, 32, 0}, {33, 34, 35}, {36, 37, 38}},
// // //        {{39, 40, 0}, {41, 42, 43}, {44, 45, 46}},
// // //        {{47, 48, 0}, {49, 50, 51}, {52, 53, 54}},
// // //        {{55, 56, 0}, {57, 58, 59}, {60, 61, 62}},
// // //        {{63, 64, 0}, {65, 66, 67}, {68, 69, 70}}


// //         List<List<Integer>> actual = typePreserveConstraint(this.maxSatEnc);
// //         List<List<Integer>> expected = Arrays.asList(
// //                 Arrays.asList(-3, -15, 17), Arrays.asList(-3, 15, -17),
// //                 Arrays.asList(-4, -15, 18), Arrays.asList(-4, 15, -18),
// //                 Arrays.asList(-5, -15, 19), Arrays.asList(-5, 15, -19),
// //                 Arrays.asList(-6, -15, 20), Arrays.asList(-6, 15, -20),
// //                 Arrays.asList(-7, -15, 21), Arrays.asList(-7, 15, -21),
// //                 Arrays.asList(-8, -15, 22), Arrays.asList(-8, 15, -22),

// //                 Arrays.asList(-3, -23, 25), Arrays.asList(-3, 23, -25),
// //                 Arrays.asList(-4, -23, 26), Arrays.asList(-4, 23, -26),
// //                 Arrays.asList(-5, -23, 27), Arrays.asList(-5, 23, -27),
// //                 Arrays.asList(-6, -23, 28), Arrays.asList(-6, 23, -28),
// //                 Arrays.asList(-7, -23, 29), Arrays.asList(-7, 23, -29),
// //                 Arrays.asList(-8, -23, 30), Arrays.asList(-8, 23, -30),

// //                 Arrays.asList(-3, -31, 33), Arrays.asList(-3, 31, -33),
// //                 Arrays.asList(-4, -31, 34), Arrays.asList(-4, 31, -34),
// //                 Arrays.asList(-5, -31, 35), Arrays.asList(-5, 31, -35),
// //                 Arrays.asList(-6, -31, 36), Arrays.asList(-6, 31, -36),
// //                 Arrays.asList(-7, -31, 37), Arrays.asList(-7, 31, -37),
// //                 Arrays.asList(-8, -31, 38), Arrays.asList(-8, 31, -38),

// //                 Arrays.asList(-3, -39, 41), Arrays.asList(-3, 39, -41),
// //                 Arrays.asList(-4, -39, 42), Arrays.asList(-4, 39, -42),
// //                 Arrays.asList(-5, -39, 43), Arrays.asList(-5, 39, -43),
// //                 Arrays.asList(-6, -39, 44), Arrays.asList(-6, 39, -44),
// //                 Arrays.asList(-7, -39, 45), Arrays.asList(-7, 39, -45),
// //                 Arrays.asList(-8, -39, 46), Arrays.asList(-8, 39, -46),

// //                 Arrays.asList(-3, -47, 49), Arrays.asList(-3, 47, -49),
// //                 Arrays.asList(-4, -47, 50), Arrays.asList(-4, 47, -50),
// //                 Arrays.asList(-5, -47, 51), Arrays.asList(-5, 47, -51),
// //                 Arrays.asList(-6, -47, 52), Arrays.asList(-6, 47, -52),
// //                 Arrays.asList(-7, -47, 53), Arrays.asList(-7, 47, -53),
// //                 Arrays.asList(-8, -47, 54), Arrays.asList(-8, 47, -54),

// //                 Arrays.asList(-3, -55, 57), Arrays.asList(-3, 55, -57),
// //                 Arrays.asList(-4, -55, 58), Arrays.asList(-4, 55, -58),
// //                 Arrays.asList(-5, -55, 59), Arrays.asList(-5, 55, -59),
// //                 Arrays.asList(-6, -55, 60), Arrays.asList(-6, 55, -60),
// //                 Arrays.asList(-7, -55, 61), Arrays.asList(-7, 55, -61),
// //                 Arrays.asList(-8, -55, 62), Arrays.asList(-8, 55, -62),

// //                 Arrays.asList(-3, -63, 65), Arrays.asList(-3, 63, -65),
// //                 Arrays.asList(-4, -63, 66), Arrays.asList(-4, 63, -66),
// //                 Arrays.asList(-5, -63, 67), Arrays.asList(-5, 63, -67),
// //                 Arrays.asList(-6, -63, 68), Arrays.asList(-6, 63, -68),
// //                 Arrays.asList(-7, -63, 69), Arrays.asList(-7, 63, -69),
// //                 Arrays.asList(-8, -63, 70), Arrays.asList(-8, 63, -70),

// //                 Arrays.asList(-9, -16, 17), Arrays.asList(-9, 16, -17),
// //                 Arrays.asList(-10, -16, 18), Arrays.asList(-10, 16, -18),
// //                 Arrays.asList(-11, -16, 19), Arrays.asList(-11, 16, -19),
// //                 Arrays.asList(-12, -16, 20), Arrays.asList(-12, 16, -20),
// //                 Arrays.asList(-13, -16, 21), Arrays.asList(-13, 16, -21),
// //                 Arrays.asList(-14, -16, 22), Arrays.asList(-14, 16, -22),

// //                 Arrays.asList(-9, -24, 25), Arrays.asList(-9, 24, -25),
// //                 Arrays.asList(-10, -24, 26), Arrays.asList(-10, 24, -26),
// //                 Arrays.asList(-11, -24, 27), Arrays.asList(-11, 24, -27),
// //                 Arrays.asList(-12, -24, 28), Arrays.asList(-12, 24, -28),
// //                 Arrays.asList(-13, -24, 29), Arrays.asList(-13, 24, -29),
// //                 Arrays.asList(-14, -24, 30), Arrays.asList(-14, 24, -30),

// //                 Arrays.asList(-9, -32, 33), Arrays.asList(-9, 32, -33),
// //                 Arrays.asList(-10, -32, 34), Arrays.asList(-10, 32, -34),
// //                 Arrays.asList(-11, -32, 35), Arrays.asList(-11, 32, -35),
// //                 Arrays.asList(-12, -32, 36), Arrays.asList(-12, 32, -36),
// //                 Arrays.asList(-13, -32, 37), Arrays.asList(-13, 32, -37),
// //                 Arrays.asList(-14, -32, 38), Arrays.asList(-14, 32, -38),

// //                 Arrays.asList(-9, -40, 41), Arrays.asList(-9, 40, -41),
// //                 Arrays.asList(-10, -40, 42), Arrays.asList(-10, 40, -42),
// //                 Arrays.asList(-11, -40, 43), Arrays.asList(-11, 40, -43),
// //                 Arrays.asList(-12, -40, 44), Arrays.asList(-12, 40, -44),
// //                 Arrays.asList(-13, -40, 45), Arrays.asList(-13, 40, -45),
// //                 Arrays.asList(-14, -40, 46), Arrays.asList(-14, 40, -46),

// //                 Arrays.asList(-9, -48, 49), Arrays.asList(-9, 48, -49),
// //                 Arrays.asList(-10, -48, 50), Arrays.asList(-10, 48, -50),
// //                 Arrays.asList(-11, -48, 51), Arrays.asList(-11, 48, -51),
// //                 Arrays.asList(-12, -48, 52), Arrays.asList(-12, 48, -52),
// //                 Arrays.asList(-13, -48, 53), Arrays.asList(-13, 48, -53),
// //                 Arrays.asList(-14, -48, 54), Arrays.asList(-14, 48, -54),

// //                 Arrays.asList(-9, -56, 57), Arrays.asList(-9, 56, -57),
// //                 Arrays.asList(-10, -56, 58), Arrays.asList(-10, 56, -58),
// //                 Arrays.asList(-11, -56, 59), Arrays.asList(-11, 56, -59),
// //                 Arrays.asList(-12, -56, 60), Arrays.asList(-12, 56, -60),
// //                 Arrays.asList(-13, -56, 61), Arrays.asList(-13, 56, -61),
// //                 Arrays.asList(-14, -56, 62), Arrays.asList(-14, 56, -62),

// //                 Arrays.asList(-9, -64, 65), Arrays.asList(-9, 64, -65),
// //                 Arrays.asList(-10, -64, 66), Arrays.asList(-10, 64, -66),
// //                 Arrays.asList(-11, -64, 67), Arrays.asList(-11, 64, -67),
// //                 Arrays.asList(-12, -64, 68), Arrays.asList(-12, 64, -68),
// //                 Arrays.asList(-13, -64, 69), Arrays.asList(-13, 64, -69),
// //                 Arrays.asList(-14, -64, 70), Arrays.asList(-14, 64, -70)
// //         );
// //         assertEquals(expected, actual);
// //     }

// //     @Test
// //     public void testCFConstraint() {
// //         initMAXSATEncoder(TempTestInput.l3, TempTestInput.l4);
// //         // v = 2, g = 2, w max = 3
// //         // 2 * 4 * 9 = 72
// //         // domainVars
// // //        {{3, 4, 5}, {6, 7, 8}},
// // //        {{9, 10, 11}, {12, 13, 14}}
// //         // CFVars
// // //        {{71, 72, 0}, {73, 74, 0}, {0, 0, 0}},
// // //        {{75, 76, 77}, {78, 79, 80}, {81, 82, 83}},
// // //        {{84, 85, 86}, {87, 88, 89}, {90, 91, 92}},


// //         List<List<Integer>> actual = CFPreserveConstraint(this.maxSatEnc);
// //         List<List<Integer>> expected = Arrays.asList(
// //                 // ------------------------------ m = 1
// //                 // g = 1, v1 = 1, v2 = 1
// //                 Arrays.asList(-3, -3, -71, 75), Arrays.asList(-3, -4, -71, 76), Arrays.asList(-3, -5, -71, 77),
// //                 Arrays.asList(-4, -3, -71, 78), Arrays.asList(-4, -4, -71, 79), Arrays.asList(-4, -5, -71, 80),
// //                 Arrays.asList(-5, -3, -71, 81), Arrays.asList(-5, -4, -71, 82), Arrays.asList(-5, -5, -71, 83),

// //                 // g = 1, v1 = 1, v2 = 2
// //                 Arrays.asList(-3, -9, -72, 75), Arrays.asList(-3, -10, -72, 76), Arrays.asList(-3, -11, -72, 77),
// //                 Arrays.asList(-4, -9, -72, 78), Arrays.asList(-4, -10, -72, 79), Arrays.asList(-4, -11, -72, 80),
// //                 Arrays.asList(-5, -9, -72, 81), Arrays.asList(-5, -10, -72, 82), Arrays.asList(-5, -11, -72, 83),

// //                 // g = 1, v1 = 2, v2 = 1
// //                 Arrays.asList(-9, -3, -73, 75), Arrays.asList(-9, -4, -73, 76), Arrays.asList(-9, -5, -73, 77),
// //                 Arrays.asList(-10, -3, -73, 78), Arrays.asList(-10, -4, -73, 79), Arrays.asList(-10, -5, -73, 80),
// //                 Arrays.asList(-11, -3, -73, 81), Arrays.asList(-11, -4, -73, 82), Arrays.asList(-11, -5, -73, 83),

// //                 // g = 1, v1 = 2, v2 = 2
// //                 Arrays.asList(-9, -9, -74, 75), Arrays.asList(-9, -10, -74, 76), Arrays.asList(-9, -11, -74, 77),
// //                 Arrays.asList(-10, -9, -74, 78), Arrays.asList(-10, -10, -74, 79), Arrays.asList(-10, -11, -74, 80),
// //                 Arrays.asList(-11, -9, -74, 81), Arrays.asList(-11, -10, -74, 82), Arrays.asList(-11, -11, -74, 83),

// //                 // g = 2, v1 = 1, v2 = 1
// //                 Arrays.asList(-6, -6, -71, 84), Arrays.asList(-6, -7, -71, 85), Arrays.asList(-6, -8, -71, 86),
// //                 Arrays.asList(-7, -6, -71, 87), Arrays.asList(-7, -7, -71, 88), Arrays.asList(-7, -8, -71, 89),
// //                 Arrays.asList(-8, -6, -71, 90), Arrays.asList(-8, -7, -71, 91), Arrays.asList(-8, -8, -71, 92),

// //                 // g = 2, v1 = 1, v2 = 2
// //                 Arrays.asList(-6, -12, -72, 84), Arrays.asList(-6, -13, -72, 85), Arrays.asList(-6, -14, -72, 86),
// //                 Arrays.asList(-7, -12, -72, 87), Arrays.asList(-7, -13, -72, 88), Arrays.asList(-7, -14, -72, 89),
// //                 Arrays.asList(-8, -12, -72, 90), Arrays.asList(-8, -13, -72, 91), Arrays.asList(-8, -14, -72, 92),

// //                 // g = 2, v1 = 2, v2 = 1
// //                 Arrays.asList(-12, -6, -73, 84), Arrays.asList(-12, -7, -73, 85), Arrays.asList(-12, -8, -73, 86),
// //                 Arrays.asList(-13, -6, -73, 87), Arrays.asList(-13, -7, -73, 88), Arrays.asList(-13, -8, -73, 89),
// //                 Arrays.asList(-14, -6, -73, 90), Arrays.asList(-14, -7, -73, 91), Arrays.asList(-14, -8, -73, 92),

// //                 // g = 2, v1 = 2, v2 = 2
// //                 Arrays.asList(-12, -12, -74, 84), Arrays.asList(-12, -13, -74, 85), Arrays.asList(-12, -14, -74, 86),
// //                 Arrays.asList(-13, -12, -74, 87), Arrays.asList(-13, -13, -74, 88), Arrays.asList(-13, -14, -74, 89),
// //                 Arrays.asList(-14, -12, -74, 90), Arrays.asList(-14, -13, -74, 91), Arrays.asList(-14, -14, -74, 92),

// //                 // ------------------------------m = 2
// //                 // g = 1, v1 = 1, v2 = 2
// //                 Arrays.asList(-3, -3, -93, 97), Arrays.asList(-3, -4, -93, 98), Arrays.asList(-3, -5, -93, 99),
// //                 Arrays.asList(-4, -3, -93, 100), Arrays.asList(-4, -4, -93, 101), Arrays.asList(-4, -5, -93, 102),
// //                 Arrays.asList(-5, -3, -93, 103), Arrays.asList(-5, -4, -93, 104), Arrays.asList(-5, -5, -93, 105),

// //                 // g = 1, v1 = 1, v2 = 2
// //                 Arrays.asList(-3, -9, -94, 97), Arrays.asList(-3, -10, -94, 98), Arrays.asList(-3, -11, -94, 99),
// //                 Arrays.asList(-4, -9, -94, 100), Arrays.asList(-4, -10, -94, 101), Arrays.asList(-4, -11, -94, 102),
// //                 Arrays.asList(-5, -9, -94, 103), Arrays.asList(-5, -10, -94, 104), Arrays.asList(-5, -11, -94, 105),

// //                 // g = 1, v1 = 2, v2 = 1
// //                 Arrays.asList(-9, -3, -95, 97), Arrays.asList(-9, -4, -95, 98), Arrays.asList(-9, -5, -95, 99),
// //                 Arrays.asList(-10, -3, -95, 100), Arrays.asList(-10, -4, -95, 101), Arrays.asList(-10, -5, -95, 102),
// //                 Arrays.asList(-11, -3, -95, 103), Arrays.asList(-11, -4, -95, 104), Arrays.asList(-11, -5, -95, 105),

// //                 // g = 1, v1 = 2, v2 = 2
// //                 Arrays.asList(-9, -9, -96, 97), Arrays.asList(-9, -10, -96, 98), Arrays.asList(-9, -11, -96, 99),
// //                 Arrays.asList(-10, -9, -96, 100), Arrays.asList(-10, -10, -96, 101), Arrays.asList(-10, -11, -96, 102),
// //                 Arrays.asList(-11, -9, -96, 103), Arrays.asList(-11, -10, -96, 104), Arrays.asList(-11, -11, -96, 105),

// //                 // g = 2, v1 = 1, v2 = 1
// //                 Arrays.asList(-6, -6, -93, 106), Arrays.asList(-6, -7, -93, 107), Arrays.asList(-6, -8, -93, 108),
// //                 Arrays.asList(-7, -6, -93, 109), Arrays.asList(-7, -7, -93, 110), Arrays.asList(-7, -8, -93, 111),
// //                 Arrays.asList(-8, -6, -93, 112), Arrays.asList(-8, -7, -93, 113), Arrays.asList(-8, -8, -93, 114),

// //                 // g = 2, v1 = 1, v2 = 2
// //                 Arrays.asList(-6, -12, -94, 106), Arrays.asList(-6, -13, -94, 107), Arrays.asList(-6, -14, -94, 108),
// //                 Arrays.asList(-7, -12, -94, 109), Arrays.asList(-7, -13, -94, 110), Arrays.asList(-7, -14, -94, 111),
// //                 Arrays.asList(-8, -12, -94, 112), Arrays.asList(-8, -13, -94, 113), Arrays.asList(-8, -14, -94, 114),

// //                 // g = 2, v1 = 2, v2 = 1
// //                 Arrays.asList(-12, -6, -95, 106), Arrays.asList(-12, -7, -95, 107), Arrays.asList(-12, -8, -95, 108),
// //                 Arrays.asList(-13, -6, -95, 109), Arrays.asList(-13, -7, -95, 110), Arrays.asList(-13, -8, -95, 111),
// //                 Arrays.asList(-14, -6, -95, 112), Arrays.asList(-14, -7, -95, 113), Arrays.asList(-14, -8, -95, 114),

// //                 // g = 2, v1 = 2, v2 = 2
// //                 Arrays.asList(-12, -12, -96, 106), Arrays.asList(-12, -13, -96, 107), Arrays.asList(-12, -14, -96, 108),
// //                 Arrays.asList(-13, -12, -96, 109), Arrays.asList(-13, -13, -96, 110), Arrays.asList(-13, -14, -96, 111),
// //                 Arrays.asList(-14, -12, -96, 112), Arrays.asList(-14, -13, -96, 113), Arrays.asList(-14, -14, -96, 114),

// //                 // ------------------------------m = 3
// //                 // g = 1, v1 = 1, v2 = 2
// //                 Arrays.asList(-3, -3, -115, 119), Arrays.asList(-3, -4, -115, 120), Arrays.asList(-3, -5, -115, 121),
// //                 Arrays.asList(-4, -3, -115, 122), Arrays.asList(-4, -4, -115, 123), Arrays.asList(-4, -5, -115, 124),
// //                 Arrays.asList(-5, -3, -115, 125), Arrays.asList(-5, -4, -115, 126), Arrays.asList(-5, -5, -115, 127),

// //                 // g = 1, v1 = 1, v2 = 2
// //                 Arrays.asList(-3, -9, -116, 119), Arrays.asList(-3, -10, -116, 120), Arrays.asList(-3, -11, -116, 121),
// //                 Arrays.asList(-4, -9, -116, 122), Arrays.asList(-4, -10, -116, 123), Arrays.asList(-4, -11, -116, 124),
// //                 Arrays.asList(-5, -9, -116, 125), Arrays.asList(-5, -10, -116, 126), Arrays.asList(-5, -11, -116, 127),

// //                 // g = 1, v1 = 2, v2 = 1
// //                 Arrays.asList(-9, -3, -117, 119), Arrays.asList(-9, -4, -117, 120), Arrays.asList(-9, -5, -117, 121),
// //                 Arrays.asList(-10, -3, -117, 122), Arrays.asList(-10, -4, -117, 123), Arrays.asList(-10, -5, -117, 124),
// //                 Arrays.asList(-11, -3, -117, 125), Arrays.asList(-11, -4, -117, 126), Arrays.asList(-11, -5, -117, 127),

// //                 // g = 1, v1 = 2, v2 = 2
// //                 Arrays.asList(-9, -9, -118, 119), Arrays.asList(-9, -10, -118, 120), Arrays.asList(-9, -11, -118, 121),
// //                 Arrays.asList(-10, -9, -118, 122), Arrays.asList(-10, -10, -118, 123), Arrays.asList(-10, -11, -118, 124),
// //                 Arrays.asList(-11, -9, -118, 125), Arrays.asList(-11, -10, -118, 126), Arrays.asList(-11, -11, -118, 127),

// //                 // g = 2, v1 = 1, v2 = 1
// //                 Arrays.asList(-6, -6, -115, 128), Arrays.asList(-6, -7, -115, 129), Arrays.asList(-6, -8, -115, 130),
// //                 Arrays.asList(-7, -6, -115, 131), Arrays.asList(-7, -7, -115, 132), Arrays.asList(-7, -8, -115, 133),
// //                 Arrays.asList(-8, -6, -115, 134), Arrays.asList(-8, -7, -115, 135), Arrays.asList(-8, -8, -115, 136),

// //                 // g = 2, v1 = 1, v2 = 2
// //                 Arrays.asList(-6, -12, -116, 128), Arrays.asList(-6, -13, -116, 129), Arrays.asList(-6, -14, -116, 130),
// //                 Arrays.asList(-7, -12, -116, 131), Arrays.asList(-7, -13, -116, 132), Arrays.asList(-7, -14, -116, 133),
// //                 Arrays.asList(-8, -12, -116, 134), Arrays.asList(-8, -13, -116, 135), Arrays.asList(-8, -14, -116, 136),

// //                 // g = 2, v1 = 2, v2 = 1
// //                 Arrays.asList(-12, -6, -117, 128), Arrays.asList(-12, -7, -117, 129), Arrays.asList(-12, -8, -117, 130),
// //                 Arrays.asList(-13, -6, -117, 131), Arrays.asList(-13, -7, -117, 132), Arrays.asList(-13, -8, -117, 133),
// //                 Arrays.asList(-14, -6, -117, 134), Arrays.asList(-14, -7, -117, 135), Arrays.asList(-14, -8, -117, 136),

// //                 // g = 2, v1 = 2, v2 = 2
// //                 Arrays.asList(-12, -12, -118, 128), Arrays.asList(-12, -13, -118, 129), Arrays.asList(-12, -14, -118, 130),
// //                 Arrays.asList(-13, -12, -118, 131), Arrays.asList(-13, -13, -118, 132), Arrays.asList(-13, -14, -118, 133),
// //                 Arrays.asList(-14, -12, -118, 134), Arrays.asList(-14, -13, -118, 135), Arrays.asList(-14, -14, -118, 136)
// //         );
// //         assertEquals(expected, actual);
// //     }
// }





