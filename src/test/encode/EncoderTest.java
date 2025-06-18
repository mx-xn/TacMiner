// package test.encode;

// import main.encode.*;
// import main.proofgraph.ProofGraph;
// import main.config.Paths;
// import resources.TempTestInput;

// import java.util.*;
// import org.junit.Test;
// import static org.junit.jupiter.api.Assertions.*;

// public class EncoderTest {

//     @Test
//     public void testConvert() {
//         List<ProofGraph> pgs = Encoder.getPGs(Encoder.inputCoqScripts(Paths.coqFilesPath + "SimpleAlgebra.json"));

//         assertEquals(pgs.get(0).toString(), "Vertices: \n" + //
//                         "intros .\n" + //
//                         "induction [a : nat] .\n" + //
//                         "simpl .\n" + //
//                         "reflexivity .\n" + //
//                         "simpl .\n" + //
//                         "rewrite [IHa : eq (Nat.add a O) a] .\n" + //
//                         "reflexivity .\n" + //
//                         "\n" + //
//                         "\n" + //
//                         "Edges: \n" + //
//                         "0: 0.0 --> 1.0, 0.1 --> 1.1, \n" + //
//                         "1: 1.0 --> 2.0, 1.1 --> 4.0, 1.2 --> 5.1, \n" + //
//                         "2: 2.0 --> 3.0, \n" + //
//                         "3: \n" + //
//                         "4: 4.0 --> 5.0, \n" + //
//                         "5: 5.0 --> 6.0, \n" + //
//                         "6: \n");
//         assertEquals(pgs.get(1).toString(), "Vertices: \n" + //
//                         "intros .\n" + //
//                         "destruct ( [a : algb] ) eqn : _o .\n" + //
//                         "reflexivity .\n" + //
//                         "reflexivity .\n" + //
//                         "\n" + //
//                         "\n" + //
//                         "Edges: \n" + //
//                         "0: 0.0 --> 1.0, 0.1 --> 1.1, \n" + //
//                         "1: 1.0 --> 2.0, 1.1 --> 3.0, \n" + //
//                         "2: \n" + //
//                         "3: \n");
//     }

// //    public static List<CoqTactic.CoqArg> generateArgs(List<Integer> ids) {
// //        return ids.stream().map(i -> new CoqTactic.CoqArg(CoqTactic.sort.PROP, "H" + i))
// //                .collect(Collectors.toList());
// //    }

//     @Test
//     public void testTacticSigs() {
//         List<CoqTactic> tactics = new ArrayList<>(Arrays.asList(
//             new CoqTactic("clear _ .", Arrays.asList(), Arrays.asList()),
//             new CoqTactic("intro H .", Arrays.asList(), Arrays.asList()),
//             new CoqTactic("simpl in _ .", Arrays.asList(), Arrays.asList()),
//             new CoqTactic("unfold _ in _ .", Arrays.asList(), Arrays.asList()),
//             new CoqTactic("apply _ in _ .", Arrays.asList(), Arrays.asList()),
//             new CoqTactic("rewrite _ in _ .", Arrays.asList(), Arrays.asList()),
//             new CoqTactic("destruct _ .", Arrays.asList(), Arrays.asList()),
//             new CoqTactic("destruct _ eqn : H .", Arrays.asList(), Arrays.asList()),
//             new CoqTactic("destruct ( beq _ T ) eqn : H2 .", Arrays.asList(), Arrays.asList())
//         ));

//         Encoder enc = new Encoder(tactics);
//         assertEquals(enc.tactics.get(0).signature, "intro _o .");
//         assertEquals(enc.tactics.get(1).signature, "simpl in _ .");
//         assertEquals(enc.tactics.get(2).signature, "unfold _ in _ .");
//         assertEquals(enc.tactics.get(3).signature, "apply _ in _ .");
//         assertEquals(enc.tactics.get(4).signature, "rewrite _ in _ .");
//         assertEquals(enc.tactics.get(5).signature, "destruct _ eqn : _o .");
//         assertEquals(enc.tactics.get(6).signature, "destruct _ eqn : _o .");
//         assertEquals(enc.tactics.get(7).signature, "destruct ( beq _ T ) eqn : _o .");

//     }
// }
