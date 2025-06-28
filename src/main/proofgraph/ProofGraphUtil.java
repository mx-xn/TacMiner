package main.proofgraph;

import main.encode.CoqProof;
import main.encode.CoqTactic;

import java.util.*;
import java.util.stream.Collectors;

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
    
}
