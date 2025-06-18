package resources;

import main.encode.CoqTactic;

import java.util.*;

public class TempTestInput {

    public static List<CoqTactic> l1 = Arrays.asList(
        /*
            intros H0, H1, H2, H3. split.
            - apply H2. apply H1 in H2. apply H2.
            - apply H2 in H3 as H4. simpl.
         */
        
        new CoqTactic(  "intros _ _ _ _ .", 
                        Arrays.asList("_goal : G1"), 
                        Arrays.asList("_goal : G2", "H1 : H1", "H2 : H2" , "H3 : H3")),
        new CoqTactic(  "split .", 
                        Arrays.asList("_goal : G2"), 
                        Arrays.asList("_goal : G3", "_goal : G4")),
        new CoqTactic(  "apply _ .", 
                        Arrays.asList("_goal : G3", "H2 : H2"), 
                        Arrays.asList("_goal : G5")),
        new CoqTactic(  "apply _ in _ .", 
                        Arrays.asList("H1 : H1", "H2 : H2"), 
                        Arrays.asList("H4 : H4")),
        new CoqTactic(  "apply _ .", 
                        Arrays.asList("_goal : G5", "H4 : H4"), 
                        Arrays.asList()),
        new CoqTactic(  "apply _ in _ as _ .", 
                        Arrays.asList("H2 : H2", "H3 : H3"), 
                        Arrays.asList("H5 : H5")),
        new CoqTactic(  "simpl .", 
                        Arrays.asList("_goal : G4"), 
                        Arrays.asList())
    );

    public static List<CoqTactic> l2 = Arrays.asList(
        /*
            intros H0, H1, H2, H3. split.
            - apply H2. apply H1 in H2. apply H2.
            - apply H2 in H3 as H4. simpl.
         */
        
        new CoqTactic(  "intros _ _ _ _ .", 
                        Arrays.asList("_goal : G1"), 
                        Arrays.asList("_goal : G2", "H1 : H1", "H2 : H2" , "H3 : H3")),
        new CoqTactic(  "split .", 
                        Arrays.asList("_goal : G2"), 
                        Arrays.asList("_goal : G3", "_goal : G4")),
        new CoqTactic(  "apply _ .", 
                        Arrays.asList("_goal : G3", "H2 : H2"), 
                        Arrays.asList("_goal : G5")),
        new CoqTactic(  "apply _ in _ .", 
                        Arrays.asList("H1 : H1", "H2 : H2"), 
                        Arrays.asList("H4 : H4")),
        new CoqTactic(  "apply _ .", 
                        Arrays.asList("_goal : G5", "H4 : H4"), 
                        Arrays.asList()),
        new CoqTactic(  "apply _ in _ as _ .", 
                        Arrays.asList("H2 : H2", "H3 : H3"), 
                        Arrays.asList("H5 : H5")),
        new CoqTactic(  "simpl .", 
                        Arrays.asList("_goal : G4"), 
                        Arrays.asList())
    );

    public static List<CoqTactic> l3 = Arrays.asList(
        /*
            intros H0, H1, H2, H3. split.
            - apply H2. apply H1 in H2. apply H2.
            - apply H2 in H3 as H4. simpl.
         */
        
        new CoqTactic(  "intros _ _ _ _ .", 
                        Arrays.asList("_goal : G1"), 
                        Arrays.asList("_goal : G2", "H1 : H1", "H2 : H2" , "H3 : H3")),
        new CoqTactic(  "split .", 
                        Arrays.asList("_goal : G2"), 
                        Arrays.asList("_goal : G3", "_goal : G4")),
        new CoqTactic(  "apply _ .", 
                        Arrays.asList("_goal : G3", "H2 : H2"), 
                        Arrays.asList("_goal : G5")),
        new CoqTactic(  "apply _ in _ .", 
                        Arrays.asList("H1 : H1", "H2 : H2"), 
                        Arrays.asList("H4 : H4")),
        new CoqTactic(  "apply _ .", 
                        Arrays.asList("_goal : G5", "H4 : H4"), 
                        Arrays.asList()),
        new CoqTactic(  "apply _ in _ as _ .", 
                        Arrays.asList("H2 : H2", "H3 : H3"), 
                        Arrays.asList("H5 : H5")),
        new CoqTactic(  "simpl .", 
                        Arrays.asList("_goal : G4"), 
                        Arrays.asList())
    );

    public static List<CoqTactic> l4 = Arrays.asList(
        /*
            intros H0, H1, H2, H3. split.
            - apply H2. apply H1 in H2. apply H2.
            - apply H2 in H3 as H4. simpl.
         */
        
        new CoqTactic(  "intros _ _ _ _ .", 
                        Arrays.asList("_goal : G1"), 
                        Arrays.asList("_goal : G2", "H1 : H1", "H2 : H2" , "H3 : H3")),
        new CoqTactic(  "split .", 
                        Arrays.asList("_goal : G2"), 
                        Arrays.asList("_goal : G3", "_goal : G4")),
        new CoqTactic(  "apply _ .", 
                        Arrays.asList("_goal : G3", "H2 : H2"), 
                        Arrays.asList("_goal : G5")),
        new CoqTactic(  "apply _ in _ .", 
                        Arrays.asList("H1 : H1", "H2 : H2"), 
                        Arrays.asList("H4 : H4")),
        new CoqTactic(  "apply _ .", 
                        Arrays.asList("_goal : G5", "H4 : H4"), 
                        Arrays.asList()),
        new CoqTactic(  "apply _ in _ as _ .", 
                        Arrays.asList("H2 : H2", "H3 : H3"), 
                        Arrays.asList("H5 : H5")),
        new CoqTactic(  "simpl .", 
                        Arrays.asList("_goal : G4"), 
                        Arrays.asList())
    );

//     public static List<CoqTactic> l1 = Arrays.asList(
//             // intros H0, H1, H2, H3. split.
//             // - apply H2. apply H1 in H2. apply H2.
//             // - apply H2 in H3 as H4. simpl.
//             new CoqTactic(intros, generateArgs(0, 4), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(apply, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply_in, generateArgs(1, 2), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(apply_in_as, generateArgs(2, 3), "1.2", false),
//             new CoqTactic(simpl, null, "1.2", true)
//     );
//     public static List<CoqTactic> l3 = Arrays.asList(
//             // intros H0, H1, H2, H3. split.
//             // - apply H2. apply H1 in H2. apply H2.
//             // - apply H2 in H3 as H4. simpl.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),

//             new CoqTactic(apply, generateArgs(0, 1), "1", false),

//             new CoqTactic(simpl, null, "1", true)
//     );

//     public static List<CoqTactic> l4 = Arrays.asList(
//             // intros H0, H1, H2, H3. split.
//             // - apply H2. apply H1 in H2. apply H2.
//             // - apply H2 in H3 as H4. simpl.
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", true),

//             new CoqTactic(apply, generateArgs(2, 1), "1.2", true)
//     );

//     public static List<CoqTactic> silly1 = Arrays.asList(
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(simpl, null, "1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1", true)
//     );


//     public static List<CoqTactic> silly2 = Arrays.asList(
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(simpl, null, "1", true)
//     );

//     public static List<CoqTactic> ex01 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - simpl. apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );

//     public static List<CoqTactic> ex02 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex11 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - simpl. apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex12 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );


//     public static List<CoqTactic> ex21 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - simpl. apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex22 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

// //            new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex23 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex31 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - simpl. apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex32 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex33 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );
//     public static List<CoqTactic> ex34 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );
//     public static List<CoqTactic> ex35 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );
//     public static List<CoqTactic> ex36 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true)

//     );
//     public static List<CoqTactic> ex37 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex38 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
// //            new CoqTactic(intro, generateArgs(1, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", true)
//     );

//     public static List<CoqTactic> ex39 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex3x = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );


//     public static List<CoqTactic> ex41 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex42 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 3, 4)), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(3, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(4, 1), "1.2", true)

//     );


//     public static List<CoqTactic> ex51 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex52 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 3, 4)), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(3, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(3, 1), "1.2", true)

//     );


//     public static List<CoqTactic> ex61 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex62 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );
//     // todo1: make sure it works for all variants of this simple example
//     // todo2: add complexity (++ types of tactics, number of graphs, #different MCS candidate node, #nodes in each graph)
//     //        record runtime, LOC, SAT input param
//     // todo3: record passing test files, run them again every time I make a change

//     public static List<CoqTactic> ex71 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex72 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(apply, generateArgs(4, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex81 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex82 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );

//     public static List<CoqTactic> ex83 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(apply, generateArgs(0, 1), "1.1", true),
//             new CoqTactic(intro, generateArgs(1, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.2", true)
//             );


//     // todo: fix
//     public static List<CoqTactic> ex91 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),
//             new CoqTactic(split, null, "1.1", false),

//             new CoqTactic(simpl, null, "1.1.1", false),
//             new CoqTactic(simpl, null, "1.1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1.1", true),

//             new CoqTactic(simpl, null, "1.1.2", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1.2", true),


//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex92 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)

//     );


//     public static List<CoqTactic> ex101 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),
//             new CoqTactic(split, null, "1.1", false),

//             new CoqTactic(simpl, null, "1.1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1.1", true),

//             new CoqTactic(simpl, null, "1.1.2", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1.2", true),


//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex102 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(1, 3), "1.2", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl_in, generateArgs(0, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex103 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex104 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(destruct_as, generateArgs(2, 3), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(3, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(3, 1), "1.2", true)
//     );

//     public static List<CoqTactic> ex105 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.2", false),
//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex111 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),
//             new CoqTactic(split, null, "1.1", false),

//             new CoqTactic(simpl, null, "1.1.1", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1.1", true),

//             new CoqTactic(simpl, null, "1.1.2", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1.2", true),


//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex112 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(1, 3), "1.2", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl_in, generateArgs(0, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex113 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex114 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(destruct_as, generateArgs(2, 3), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(3, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(3, 1), "1.2", true)
//     );

//     public static List<CoqTactic> ex115 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.2", false),
//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex116 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(Arrays.asList(0, 2, 3)), "1.1", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),
//             new CoqTactic(split, null, "1.1", false),

//             new CoqTactic(apply, generateArgs(2, 1), "1.1.1", true),

//             new CoqTactic(simpl, null, "1.1.2", false),
//             new CoqTactic(simpl, null, "1.1.2", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1.2", true),


//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex117 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(destruct_as, generateArgs(1, 3), "1.2", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.1", true),

//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(0, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex118 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(0, 1), "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(1, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.2", true)
//     );


//     public static List<CoqTactic> ex119 = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(destruct_as, generateArgs(2, 3), "1.2", false),
//             new CoqTactic(apply, generateArgs(4, 1), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(3, 1), "1.2", false),
//             new CoqTactic(apply, generateArgs(3, 1), "1.2", true)
//     );

//     public static List<CoqTactic> ex11x = Arrays.asList(
//             // intro H0. split.
//             // - simpl. apply H0.
//             // - apply H0.
//             new CoqTactic(intro, generateArgs(0, 1), "1", false),
//             new CoqTactic(split, null, "1", false),

//             new CoqTactic(intro, generateArgs(1, 1), "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(simpl, null, "1.1", false),
//             new CoqTactic(apply, generateArgs(1, 1), "1.1", true),

//             new CoqTactic(destruct_as, generateArgs(0, 3), "1.2", false),
//             new CoqTactic(simpl_in, generateArgs(2, 1), "1.2", false),
//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(simpl, null, "1.2", false),
//             new CoqTactic(apply, generateArgs(2, 1), "1.2", true)
//     );
}
