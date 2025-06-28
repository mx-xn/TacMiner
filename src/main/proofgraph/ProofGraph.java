package main.proofgraph;

import java.util.*;
import java.util.stream.Collectors;

import main.encode.CoqTactic;

public class ProofGraph {

    // Represents a labeled edge (tactic dependency) in a proof graph
    public static class Edge {
        public int u, v; // Edge from node u to v
        public int fromPos, toPos; // Edge label with position of arguments

        public Edge(int u, int v, int fromPos, int toPos) {
            this.u = u;
            this.v = v;
            this.fromPos = fromPos;
            this.toPos = toPos;
        }

        // A partial edge consisting only of the source node
        public Edge(int u, int fromPos) {
            this(u, -1, fromPos, -1);
        }

        // Completion of a partial edge
        public Edge(Edge source, int v, int toPos) {
            this(source.u, v, source.fromPos, toPos);
        }

        @Override
        public boolean equals(Object o){
            if(! (o instanceof Edge)) return false;

            Edge edge = (Edge) o;
            return this.u == edge.u && this.v == edge.v && this.fromPos == edge.fromPos && this.toPos == edge.toPos;
        }

        @Override
        public int hashCode() {
            return Integer.hashCode(u) + Integer.hashCode(v) + Integer.hashCode(fromPos) + Integer.hashCode(toPos);
        }

        @Override
        public String toString() {
            return u + "." + fromPos + " --> " + v + "." + toPos;
        }
    }

    // Vertices are tactics. These vertices are shared by the corresponding CoqProof object!
    public List<CoqTactic> vertices;
    // Edges are tactic dependencies, represented by an adjacency list
    public List<List<Edge>> adjList;

    // Maps propositions to their source node
    public Map<String, Edge> propMap; 

    public ProofGraph(List<CoqTactic> tactics) {
        vertices = tactics;
        adjList = new ArrayList<>();
        for(int i = 0; i < vertices.size(); i++) {
            adjList.add(new ArrayList<>());
        }
        propMap = new HashMap<>();

        buildGraph();
    }

    public Map<String, Integer> getSigCount() {
        Map<String, Integer> res = new HashMap<>();
        for (CoqTactic t: this.vertices) {
            res.put(t.sig_no_out_arg, res.getOrDefault(t.sig_no_out_arg, 0) + 1);
        }
        return res;
    }

    private void buildGraph() {
        // Build dependency graph
        for (int i = 0; i < vertices.size(); i++) {
            CoqTactic tactic = vertices.get(i);

            for (int j = 0; j < tactic.outputs.size(); j++) {
                CoqTactic.Prop res = tactic.outputs.get(j);
                String name = res.name;
                if (res.type.equals(CoqTactic.PROP_TYPE.GOAL)) {
                    name = name.split(" : ")[0];
                }
                propMap.put(name, new Edge(i, j));
            }
        }

        for (int i = 0; i < vertices.size(); i++) {
            CoqTactic tactic = vertices.get(i);
            for (int j = 0; j < tactic.inputs.size(); j++) {
                CoqTactic.Prop arg = tactic.inputs.get(j);
                String argName = arg.name;
                if (arg.type.equals(CoqTactic.PROP_TYPE.GOAL)) argName = argName.split(" : ")[0];
                if (propMap.keySet().contains(argName)) {
                    Edge edge = new Edge(propMap.get(argName), i, j);
                    if (edge.u == edge.v) continue;
                    adjList.get(edge.u).add(edge);
                }
            }
        }
    }

    public void checkCycle(int node, Set<Integer> ancestors) {
        if (ancestors.contains(node)) {
        //    System.out.println(vertices);
           throw new IllegalArgumentException("Cycle detected!");
        }
        ancestors.add(node);

        for (Edge e : adjList.get(node)) {
            checkCycle(e.v, ancestors);
        }

        ancestors.remove(node);
    }

    // returns the adjList, where edges from u to v with different position pairs
    // are treated as the same edge
    public List<List<Edge>> simplifiedEdges() {
        List<List<Edge>> simpleEdges = new ArrayList<>();
        for (List<Edge> edgesFromU: this.adjList) {
            simpleEdges.add(edgesFromU.stream()
                    .map(e -> new Edge(e.u, e.v, -1, -1))
                    .distinct().collect(Collectors.toList()));
        }
        return simpleEdges;
    }

    public int getNthChildID(int uID, int n) {
        List<Edge> edges = this.adjList.get(uID);
        for (Edge e : edges) {
            if (e.fromPos == n)
                return e.v;
        }
        return -1;
    }

    public int numReachableVertices(int uID) {
        // do a DFS from vID
        Set<Integer> visited = new HashSet<>();
        dfs(uID, visited);
        return visited.size();
    }
    private void dfs(int uID, Set<Integer> visited) {
        visited.add(uID);
        for (Edge e : adjList.get(uID)) {
            if (!visited.contains(e.v)) {
                dfs(e.v, visited);
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("Vertices: \n");
        for (CoqTactic each: vertices) {
            sb.append(each.condensedToString() + "\n");
        }
        sb.append("\n\nEdges: \n");
        for (int u = 0; u < vertices.size(); u++) {
            sb.append(u + ": ");
            for (Edge each: adjList.get(u)) {
                sb.append(each.toString() + ", ");
            }
            sb.append("\n");
        }
        return sb.toString();
    }

}