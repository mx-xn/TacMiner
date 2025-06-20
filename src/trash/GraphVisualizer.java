package trash;

import main.encode.*;
import main.proofgraph.ProofGraph;
import main.proofgraph.ProofGraph.Edge;

import org.graphstream.graph.*;
import org.graphstream.graph.implementations.*;

import java.util.*;
import java.util.stream.Collectors;

public class GraphVisualizer {

    public static void main(String[] args) {
        // Create a new graph
        CoqProof proof = new CoqProof("dummy_lemma", TempTestInput.l1);
        proof.initProofGraph();
        visualize(proof.pgraph);
    }

    public static void visualize(ProofGraph pgraph) {
        System.setProperty("org.graphstream.ui", "swing");
        Graph graph = new MultiGraph("ExampleGraph");
        System.out.println("in visualizing");

        // Add nodes
        for (CoqTactic tactic : pgraph.vertices) {
            String name = tactic.id + ": " + tactic.signature;
            graph.addNode(name);
            graph.getNode(name).setAttribute("id", tactic.id);
            graph.getNode(name).setAttribute("sig", tactic.signature);
            graph.getNode(name).setAttribute("args", String.join(" ", tactic.inputs.stream().map(n -> n.name).collect(Collectors.toList())));
            graph.getNode(name).setAttribute("res", String.join(" ", tactic.outputs.stream().map(n -> n.name).collect(Collectors.toList())));
        }

        // Add edges
        for (List<ProofGraph.Edge> adj : pgraph.adjList) {
            for (ProofGraph.Edge e : adj) {
                String from = pgraph.vertices.get(e.u).id + ": " + pgraph.vertices.get(e.u).signature;
                String to = pgraph.vertices.get(e.v).id + ": " + pgraph.vertices.get(e.v).signature;
                graph.addEdge(e.toString(), from, to, true);
            }
        }

        for (Node node : graph) {
            node.setAttribute("ui.label", node.getAttribute("id") + ": " + node.getAttribute("sig"));
        }
        for (Edge e : graph.edges().collect(Collectors.toList())) {
            e.setAttribute("ui.label", e.getId());
        }

        String styleSheet =
                "node {" +
                        "	shape: circle;" +
                        "   fill-color: rgba(255,0,0,128);" +
                        "   text-background-mode: plain; text-background-color: #EB2;" +
                        "   size: 30px;"  +
                        "   size-mode: fit;" +
                        "   text-size: 25px;"  +
                        "   text-alignment: under;"  +
                        "}" +
                        "edge {" +
                        "   arrow-shape: arrow;"  +
                        "   arrow-size: 10px, 4px;"  +
                        "   text-size: 25px;"  +
                "}";

        graph.setAttribute("ui.stylesheet", styleSheet);
        graph.setAttribute("ui.quality");

        // Enable graph display
        graph.display(true);
    }
}