import org.graphstream.graph.*;
import org.graphstream.graph.implementations.SingleGraph;

import java.util.*;

public class MaxSATDebugger {
    static List<int[]> map = new ArrayList<>();  // map[g][v]: v is mapped to map[g][v] in g
    // ------------------------------------------------------
    // for debugging purposes
    // ------------------------------------------------------

    // input: maxSATEncoder, output: a list of graph object that reflects the mapping
    public static List<Graph> getGraphList(MaxSatEncoder enc, List<Integer> sol) {
        List<Graph> res = new ArrayList<>();

        // get the reflected input graphs
        for (int g = 0; g < enc.numGraphs; g++) {
            // for each graph, if there is a mapping f(v, g, w), add w (and its type)
            Graph graph = new SingleGraph("input " + (g + 1));

            map.add(new int[enc.vCount]);
            Arrays.fill(map.get(map.size() - 1), -1);

            addVertices(enc, sol, g, graph);
            addEdges(enc, sol, g, graph);

            res.add(graph);
        }
        return res;
    }

    public static void displayGraphs(MaxSatEncoder enc, List<Integer> sol) {
        List<Graph> graphs = getGraphList(enc, sol);
        for (int i = 0; i < graphs.size(); i++) {
            System.setProperty("org.graphstream.ui", "swing");
            String styleSheet =
                    "node {" +
                            "	shape: circle;" +
                            "   fill-color: rgba(255,0,0,128);" +
                            "   text-background-mode: plain; text-background-color: #EB2;" +
                            "   size: 30px;"  +
//                        "   size-mode: fit;" +
                            "   text-size: 25px;"  +
                            "   text-alignment: under;"  +
                            "}" +
                            "edge {" +
                            "   arrow-shape: arrow;"  +
                            "   arrow-size: 10px, 4px;"  +
                            "   text-size: 25px;"  +
                            "   text-alignment: along;"  +
                            "}";

            Graph graph = graphs.get(i);
            graph.setAttribute("ui.stylesheet", styleSheet);
            graph.setAttribute("ui.quality");

            // Enable graph display
            graph.display(true);
        }
    }

    public static void addVertices(MaxSatEncoder enc, List<Integer> sol, int g, Graph graph) {
        for (int w = 0; w < enc.gVertexSize(g); w++) {
            // see if there is any v that gets mapped to w
            for (int v = 0; v < enc.vCount; v++) {
                if (sol.contains(enc.domainVars[v][g][w])) {
                    map.get(map.size() - 1)[v] = w;
                    graph.addNode(Integer.toString(w));
                    Node n = graph.getNode(Integer.toString(w));
                    n.setAttribute("name", getTacSig(enc, sol, g + 1, w).toString());
                    n.setAttribute("ui.label", n.getId() + ": " + n.getAttribute("name"));
                    break;
                }
            }
        }
    }

    public static void addEdges(MaxSatEncoder enc, List<Integer> sol, int g, Graph graph) {
        for (int v1 = 0; v1 < enc.vCount; v1++) {
            for (int v2 = 0; v2 < enc.vCount; v2++) {
                for (int m = 0; m < enc.metadataList.size(); m++) {
                    int add = m * enc.vCFCount;
                    if (sol.contains(enc.CFVars[0][v1][v2] + add)) {
                        String name = "(" + m + ": " + v1 + "," + v2 + ")";
                        graph.addEdge(name,
                                Integer.toString(map.get(g)[v1]),
                                Integer.toString(map.get(g)[v2]), true);
                        graph.getEdge(name).setAttribute("ui.label",
                                enc.metadataList.get(m).toString());
                        break;
                    }
                }
            }
        }
    }

    public static String getTacSig(MaxSatEncoder enc, List<Integer> sol, int g, int w) {
        for (int t = 0; t < enc.tacticList.size(); t++) {
            if (sol.contains(enc.typeVars[t][g][w]))
                return enc.tacticList.get(t);
        }
        return null;
    }

    // for second round:
    // given a list of vertex id's, print out if each one reaches each one
    public static void printReachability(List<Integer> vertices, MaxSatEncoder enc, int g,
                                         int[][] mcsVarMap, int[][][] reachMap,
                                         List<Integer> sol1, List<Integer> sol2) {
        for (int k = 0; k <= g; k++) {
            System.out.println("start graph " + k + "---------------------");
            for (int i = 0; i < vertices.size(); i++) {
                for (int j = 0; j < vertices.size(); j++) {
                    int v1 = vertices.get(i);
                    int v2 = vertices.get(j);

                    if (sol2.contains(reachMap[k][v1][v2])) {
                        // v1 reaches v2 in graph k

                        // get the actual vertex id in graph g > 0
                        if (k > 0) {
                            v1 = mcsVarMap[k - 1][v1];
                            v2 = mcsVarMap[k - 1][v2];
                        }

                        String t1 = getTacSig(enc, sol1, k, v1);
                        String t2 = getTacSig(enc, sol1, k, v2);

                        System.out.println(v1 + ": " + t1 + " reaches " +
                        v2 + ": " + t2);
                    }
                }
            }
            System.out.println("end graph " + k + "---------------------");
        }
    }

    public static void printThruReachability(List<Integer> vertices, MaxSatEncoder enc, int g,
                                         int[][] mcsVarMap, int[][][][] reachThruMap,
                                         List<Integer> sol1, List<Integer> sol2) {
        for (int k = 0; k <= g; k++) {
            System.out.println("start graph " + k + "---------------------");
            for (int i = 0; i < vertices.size(); i++) {
                for (int j = 0; j < vertices.size(); j++) {
                    for (int l = 0; l < vertices.size(); l++) {
                        int v1 = vertices.get(i);
                        int v2 = vertices.get(j);
                        int v3 = vertices.get(l);

                        if (sol2.contains(reachThruMap[k][v1][v2][v3])) {
                            // v1 reaches v2 in graph k

                            // get the actual vertex id in graph g > 0
                            if (k > 0) {
                                v1 = mcsVarMap[k - 1][v1];
                                v2 = mcsVarMap[k - 1][v2];
                                v3 = mcsVarMap[k - 1][v3];
                            }

                            String t1 = getTacSig(enc, sol1, k, v1);
                            String t2 = getTacSig(enc, sol1, k, v2);
                            String t3 = getTacSig(enc, sol1, k, v3);

                            System.out.println(v1 + ": " + t1 + " reaches " +
                                    v3 + ": " + t3 + " thru " + v2 + ": " + t2);
                        }

                    }
                }
            }
            System.out.println("end graph " + k + "---------------------");
        }
    }
}
