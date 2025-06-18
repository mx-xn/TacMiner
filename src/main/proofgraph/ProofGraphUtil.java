package main.proofgraph;

import main.Engine;
import main.Main;
import main.encode.CoqProof;
import main.encode.CoqTactic;

import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

import static main.config.Paths.*;
import static main.maxsat.MaxSATUtil.writeTo;

public class ProofGraphUtil {
    // Function to perform DFS on the graph
    public static void dfs(int v, ProofGraph pg, Set<Integer> visited) {
        // Mark the current node as visited
        visited.add(v);

        // Recur for all the vertices adjacent to this vertex
        for (ProofGraph.Edge e : pg.adjList.get(v)) {
            if (!visited.contains(e.v)) {
                dfs(e.v, pg, visited);
            }
        }
    }

    // Function to return all reachable vertices from a given vertex
    public static List<CoqTactic> getReachableVertices(int startVertex, ProofGraph pg) {
        Set<Integer> visited = new LinkedHashSet<>();
        dfs(startVertex, pg, visited);

        return new ArrayList<>(visited).stream().map(id -> pg.vertices.get(id)).collect(Collectors.toList());
    }

    public static List<ProofGraph> getBranchSubgraphs(ProofGraph pg) {
        List<ProofGraph> subgraphs = new ArrayList<>();

        // go through the vertices, for each vertex v that splits > 1 goals, where each of the goal corresponds to an edge to one of v's children w,
        // get the subgraph branching off from w, and add to the list
        for (int v = 0; v < pg.vertices.size(); v++) {
            // get all the edges where the fromPos corresponds to a goal
            CoqTactic tactic = pg.vertices.get(v);
            List<ProofGraph.Edge> goalEdges = pg.adjList.get(v)
                    .stream().filter(e -> tactic.outputs.get(e.fromPos).type.equals(CoqTactic.PROP_TYPE.GOAL))
                    .collect(Collectors.toList());
            if (goalEdges.size() <= 1) continue;
            // current tactic splits to multiple goals, for each of its children, do a search and get all the vertices
            for (int childID: goalEdges.stream().map(e -> e.v).collect(Collectors.toList())) {
                List<CoqTactic> subgraphVertices = getReachableVertices(childID, pg);
                if (subgraphVertices.size() > 1) {
                    subgraphs.add(new ProofGraph(subgraphVertices));
                }
            }
        }
        return subgraphs;
    }

    public static boolean areSubgraphsSimilar(ProofGraph pg1, ProofGraph pg2) {
//        if (pg1.vertices.size() >= 12 && pg2.vertices.size() >= 12) return false;
//        double sizePercentage = 70;
//        double sizeDivision = (double)pg1.vertices.size() / (double)pg2.vertices.size();
//        if (sizeDivision < sizePercentage / 100.0 || sizeDivision > 100.0 / sizePercentage) return false;
//
//        // get types of tactics T1, T2, if intersection is within x percent, return false
//        double typeOverlapBar = 0.7;
//        List<String> sigsPG1 = getDistinctSigsOfGraph(pg1);
//        List<String> sigsPG2 = getDistinctSigsOfGraph(pg2);
//
//        List<String> intersection = new ArrayList<>(sigsPG1);
//        intersection.retainAll(sigsPG2);
//
//        if ((double)intersection.size() / (double)sigsPG1.size() < typeOverlapBar) return false;
//        if ((double)intersection.size() / (double)sigsPG2.size() < typeOverlapBar) return false;
//
        return true;
    }

    public static List<String> getDistinctSigsOfGraph(ProofGraph pg) {
        return pg.vertices.stream().map(v -> v.sig_no_out_arg)
                .distinct()
                .collect(Collectors.toList());
    }

    public static List<CoqProof> getSplitLemmasFromOneProof(CoqProof p) {
        if (p.tactics.isEmpty()) return new ArrayList<>();
        if (p.pgraph == null) p.pgraph = new ProofGraph(p.tactics);

        List<ProofGraph> subgraphs = getBranchSubgraphs(p.pgraph);

        List<CoqProof> lemmas =  subgraphs.stream().map(g -> new CoqProof(p.lemma_name + "_" + subgraphs.indexOf(g), g.vertices, "")).collect(Collectors.toList());
        for (CoqProof l: lemmas) {
            l.pgraph = subgraphs.get(lemmas.indexOf(l));
        }
        return lemmas;
    }
    
//    public static List<CoqProof> extractWithinOneGraph(ProofGraph pg, int timeout) {
//        System.out.println("extracting next graph");
//        // get all the splitted goals, store all splitted goals
//        List<ProofGraph> subgraphs = getBranchSubgraphs(pg);
//        List<String> subgoals = new ArrayList<>();
//        for (ProofGraph subgraph: subgraphs) {
//            // store the first subgoal of each subgraph
//            CoqTactic root = subgraph.vertices.get(0);
//            for (CoqTactic.Prop input: root.inputs) {
//                if (input.type.equals(CoqTactic.PROP_TYPE.HYP)) continue;
//                // if type is goal, extract the goal, and store the string
//                subgoals.add(input.simpleName());
//            }
//        }
//
//        // for each pair, if they are similar enough, run maxSAT, and store extracted tactics
//        Main.Config dummyConfig = new Main.Config(-1, timeout, "", "", "", false);
//        List<CoqProof> customTactics = new ArrayList<>();
//        for (int i = 0; i < subgraphs.size(); i++) {
//            for (int j = i + 1; j < subgraphs.size(); j++) {
//                if (areSubgraphsSimilar(subgraphs.get(i), subgraphs.get(j))) {
//                    System.out.println("extracting subgoal " + i + " and subgoal " + j);
//                    // extract common tactics
//                    Engine engine = new Engine(Arrays.asList(subgraphs.get(i), subgraphs.get(j)), dummyConfig, true);
//                    engine.runWithTimeout(dummyConfig.timeout);
//                    if (engine.mcsScript == null) continue;
//                    for (CoqProof mcs: engine.mcsScript) {
//                        if (!mcs.tactics.isEmpty()) {
//                            customTactics.add(mcs);
//                        }
//                    }
//                }
//            }
//        }
//
//        // store goals in one file
////        writeTo(String.join("\n\n" ,subgoals), proofSearchPath + pgName + "-subgoals.txt");
//
//        return customTactics;
////        writeTo(customTactics.toString(), compressionEvalPath + "temp/" + pgName + "-tactics.txt");
//    }
}
