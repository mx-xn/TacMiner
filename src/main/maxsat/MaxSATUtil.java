package main.maxsat;

import main.encode.*;
import main.proofgraph.ProofGraph;
import main.config.Paths;

import java.io.*;
import java.util.*;
import java.util.stream.*;

import static main.encode.CoqTactic.serializeArgs;

public class MaxSATUtil {

    public static void addSecondObjectives(MaxSatEncoder enc, List<String> output, int weight) {
        for (int p = 1; p <= enc.mcsVCount; p++) {
            output.add(weight + " " + -p + " " + 0);
        }
    }

    public static List<List<Integer>> getReachableConstants(MaxSatEncoder enc, int[][][] reachMap,
                                                            int[][][][] reachThruMap, int[][] mcsVarMap,
                                                      List<Integer> vertices, List<Integer> sol) {
        List<List<Integer>> res = new ArrayList<>();

        // each vertex reaches itself, but cannot reach thru itself
        for (int g = 0; g < reachMap.length; g++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                res.add(Arrays.asList(reachMap[g][v][v]));
                res.add(Arrays.asList(-reachThruMap[g][v][v][v]));
                for (int u = 0; u < enc.mcsVCount; u++) {
                    if (v == u) continue;
                    res.add(Arrays.asList(-reachThruMap[g][v][v][u]));
                    res.add(Arrays.asList(-reachThruMap[g][v][u][u]));
                }
            }
        }

        // check for non-edges in MCS
        for (int v = 0; v < enc.mcsVCount; v++) {
            for (int u = 0; u < enc.mcsVCount; u++) {
                // check if there is an edge (v -> u) in MCS
                if (v == u) continue;
                int vMCS = vertices.get(v) - 1;
                int uMCS = vertices.get(u) - 1;
                String vt = findSig(enc, sol, vMCS, 0);
                String ut = findSig(enc, sol, uMCS, 0);

                // if (v, u) is not an edge, r(g, v, u) iff r(g, v, w, u)
                if (ifEdgeInG(vMCS, uMCS, 0, enc, sol)) {
                    List<Integer> edgesG1 = new ArrayList<>();
                    List<Integer> edgesG2 = new ArrayList<>();
                    for (int m = 0; m < enc.metadataList.size(); m++) {
                        int add = m * enc.vCFCount;
                        if (sol.contains(enc.CFVars[1][mcsVarMap[0][v]][mcsVarMap[0][u]] + add)) {
                            edgesG1.add(m);
                        }
                        if (sol.contains(enc.CFVars[2][mcsVarMap[1][v]][mcsVarMap[1][u]] + add)) {
                            edgesG2.add(m);
                        }
                    }

                    if (edgesG1.equals(edgesG2)) {
//                        System.out.println("adding reach thru from " + v + " to " + u + ": " + reachMap[0][v][u]);
                        res.add(Arrays.asList(reachMap[0][v][u]));
                        continue;
                    }
                }

//                System.out.println(vMCS + " of type " + vt + "-!->" +
//                        uMCS + " of type " + ut);
                List<Integer> oneConstraint = new ArrayList<>(Arrays.asList(-reachMap[0][v][u]));
//                System.out.println("processing not reach thru from " + v + " to " + u + ": " + reachMap[0][v][u]);
                for (int w = 0; w < enc.mcsVCount; w++) {
                    if (w == v || w == u) continue;
                    oneConstraint.add(reachThruMap[0][v][w][u]);
                    res.add(Arrays.asList(-reachThruMap[0][v][w][u], reachMap[0][v][u]));
                }
                res.add(oneConstraint);
                //    System.out.println(vMCS + " of type " + vt + "-->" +
                //            uMCS + " of type " + ut);
            }
        }

        // if there is an edge between (v, u) at g, v reaches u at g
        for (int g = 0; g < enc.numGraphs; g++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int u = 0; u < enc.mcsVCount; u++) {                    
                    // get the vertices vG, uG which v and u are mapped to in V_g
                    int vG = mcsVarMap[g][v];
                    int uG = mcsVarMap[g][u];
                    // check if there is an edge (vG -> uG) in G
                    if (ifEdgeInG(vG, uG, g+1, enc, sol)) {
//                        System.out.println(vG + " reaches " + uG + " in " + (g + 1) + ": " + reachMap[g+1][v][u]);
                        // v reaches u thru v, v reaches u thru u
                        res.add(Arrays.asList(reachMap[g+1][v][u]));
//                        System.out.println(v + " reaches " + u + " in " + g + ", outputting " + reachMap[g+1][v][u]);
                    }
                }
            }
        }
        return res;
    }

    // returns true if there is an edge v -> u in MCS(if g = 0) / Gg(if g > 0),
    //         false otherwise
    public static boolean ifEdgeInG(int v, int u, int g, MaxSatEncoder enc, List<Integer> sol) {
        // returns true if edges in v, u are exactly the same, return false otherwise
        for (int m = 0; m < enc.metadataList.size(); m++) {
            int add = m * enc.vCFCount;
            if (sol.contains(enc.CFVars[g][v][u] + add)) {
                return true;
            }
        }

        return false;
    }

    public static String findSig(MaxSatEncoder enc, List<Integer> sol, int v, int g) {
        for (int t = 0; t < enc.tacticList.size(); t++) {
            if (sol.contains(enc.typeVars[t][g][v])) {
                return enc.tacticList.get(t);
            }
        }
        return null;
    }



    // output the bool var map that represents CC(k, v): if v belongs to CC_k
    public static int[][] getCCMap(MaxSatEncoder enc) {
        int numPrevVars = enc.mcsVCount;
        int[][] ccMap = new int[enc.mcsVCount][enc.mcsVCount];

        int i = numPrevVars + 1;
        for (int k = 0; k < enc.mcsVCount; k++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                ccMap[k][v] = i++;
            }
        }
        return ccMap;
    }

    // output the bool var map that represents r(g, v, u): if v reaches u at graph g
    public static int[][][] getReachMap(MaxSatEncoder enc) {
        int numPrevVars = enc.mcsVCount * (enc.mcsVCount+1);
        int[][][] reachMap = new int[enc.numGraphs + 1][enc.mcsVCount][enc.mcsVCount];

        int i = numPrevVars + 1;
        for (int g = 0; g <= enc.numGraphs; g++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int u = 0; u < enc.mcsVCount; u++) {
                    reachMap[g][v][u] = i++;
                }
            }
        }
        return reachMap;
    }

    public static int[][][][] getReachThruMap(MaxSatEncoder enc) {
        int numPrevVars = enc.mcsVCount * (enc.mcsVCount+1) +
                enc.mcsVCount * enc.mcsVCount * (enc.numGraphs + 1);
        int[][][][] reachThruMap = new int[enc.numGraphs + 1][enc.mcsVCount][enc.mcsVCount][enc.mcsVCount];

        int i = numPrevVars + 1;
        for (int g = 0; g <= enc.numGraphs; g++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int w = 0; w < enc.mcsVCount; w++) {
                    for (int u = 0; u < enc.mcsVCount; u++) {
                        reachThruMap[g][v][w][u] = i++;
                    }
                }
            }
        }
        return reachThruMap;
    }

    public static int[][][] getBridgeMap(MaxSatEncoder enc) {
        int[][][][] reachThruMap = new int[enc.numGraphs + 1][enc.mcsVCount][enc.mcsVCount][enc.mcsVCount];
        int numPrevVars = enc.mcsVCount * (enc.mcsVCount+1) +
                enc.mcsVCount * enc.mcsVCount * (enc.numGraphs + 1) +
                enc.mcsVCount * enc.mcsVCount * enc.mcsVCount * (enc.numGraphs + 1);
        int[][][] bridgeMap = new int[enc.mcsVCount][enc.mcsVCount][enc.mcsVCount];

        int i = numPrevVars + 1;
        for (int w = 0; w < enc.mcsVCount; w++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int u = 0; u < enc.mcsVCount; u++) {
                    bridgeMap[w][v][u] = i++;
                    // if w reaches both v and u
                }
            }
        }
        return bridgeMap;
    }

    /* returns a list of list map, where map[i] represents the mapping from V* to V_i,
       while map[i][j] represents the vertex id in V_g where v_j in V* is mapped to
     */
    public static int[][] getMappingFromMCS(MaxSatEncoder enc, List<Integer> vertices, List<Integer> sol) {
        int[][] map = new int[enc.numGraphs][enc.mcsVCount];
        for (int g = 0; g < enc.numGraphs; g++) {
            for (int v = 0; v < vertices.size(); v++) {
                for (int w = 0; w < enc.gVertexSize(g); w++) {
                    if (sol.contains(enc.domainVars[vertices.get(v)-1][g][w])) {
//                        System.out.println(vertices.get(v) + " in MCS is mapped to " + w);
                        map[g][v] = w;
                        break;
                    }
                }
            }
        }
        return map;
    }

    /*
     if there exists any vertex v in CC_k, then CC_k exists
     */
    public static List<List<Integer>> ccExistenceConstraint(MaxSatEncoder enc, int[][] ccMap) {
        List<List<Integer>> res = new ArrayList<>();
        for (int k = 0; k < enc.mcsVCount; k++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                res.add(Arrays.asList(-ccMap[k][v], k+1));
            }
        }
        return res;
    }

    public static List<List<Integer>> allVertexMappedConstraint(MaxSatEncoder enc, int[][] ccMap) {
        List<List<Integer>> res = new ArrayList<>();
        for (int v = 0; v < enc.mcsVCount; v++) {
            int finalV = v;
            res.add(IntStream.range(0, enc.mcsVCount)
                    .map(k -> ccMap[k][finalV]).boxed()
                    .collect(Collectors.toList()));
        }
        return res;
    }

    public static List<List<Integer>> disconnectedConstraint(MaxSatEncoder enc, int[][] ccMap,
                                                             int[][][] reachMap) {
        List<List<Integer>> res = new ArrayList<>();
        for (int v = 0; v < enc.mcsVCount; v++) {
            for (int u = 0; u < enc.mcsVCount; u++) {
                for (int k = 0; k < enc.mcsVCount; k++) {
                    res.add(Arrays.asList(
                            reachMap[0][v][u], reachMap[0][u][v],
                            -ccMap[k][v], -ccMap[k][u]));
                }
            }
        }
        return res;
    }

    public static List<List<Integer>> additionalReachableConstraint(MaxSatEncoder enc, int[][][] reachMap,
                                                                   int[][][][] reachThruMap) {
        List<List<Integer>> res = new ArrayList<>();
        for (int g = 0; g < reachMap.length; g++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int u = 0; u < enc.mcsVCount; u++) {
                    // if v reaches u, v != u, u cannot reach v
                    if (u == v) continue;
                    res.add(Arrays.asList(-reachMap[g][v][u], -reachMap[g][u][v]));
                    for (int w = 0; w < enc.mcsVCount; w++) {
                        // if v reaches u thru w, v cannot reach w thru u
                        if (w == v || w == u) continue;
                        res.add(Arrays.asList(-reachThruMap[g][v][w][u], -reachThruMap[g][v][u][w]));
                    }
                }
            }
        }
        return res;
    }

    public static List<List<Integer>> bridgeConstraint(MaxSatEncoder enc, int[][][] reachMap,
                                                       int[][][] bridgeMap) {
        List<List<Integer>> res = new ArrayList<>();
        // w reaches both u and v iff w reaches u and w reaches v
        for (int w = 0; w < enc.mcsVCount; w++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int u = 0; u < enc.mcsVCount; u++) {
                    // b(w, v, u) --> r(0, w, v) ^ r(0, w, u)
                    // !b(w, v, u) or r(0, w, v), !b(w, v, u) or r(0, w, u)
                    res.add(Arrays.asList(-bridgeMap[w][v][u], reachMap[0][w][v]));
                    res.add(Arrays.asList(-bridgeMap[w][v][u], reachMap[0][w][u]));

                    // r(0, w, v) ^ r(0, w, u) --> b(w, v, u)
                    // !r(0, w, v) or !r(0, w, u) or b(w, v, u)
                    res.add(Arrays.asList(-reachMap[0][w][v], -reachMap[0][w][u], bridgeMap[w][v][u]));
                }
            }
        }
        return res;
    }

    // NOT CORRECT
    // public static List<List<Integer>> CCReachabilityConstraint(MaxSatEncoder enc, int[][] ccMap,
    //                                                             int[][][] reachMap) {
    //     List<List<Integer>> res = new ArrayList<>();
    //     for (int g = 1; g <= enc.numGraphs; g++) {
    //         for (int v = 0; v < enc.mcsVCount; v++) {
    //             for (int u = 0; u < enc.mcsVCount; u++) {
    //                 for (int k = 0; k < enc.mcsVCount; k++) {
    //                     res.add(Arrays.asList(
    //                             reachMap[0][v][u],
    //                             reachMap[0][u][v],
    //                             -ccMap[k][v], -ccMap[k][u]));
    //                 }
    //             }
    //         }
    //     }
    //     return res;
    // }

    public static List<List<Integer>> pathReachabilityConstraint(MaxSatEncoder enc, int[][] ccMap,
                                                                int[][][] reachMap, int[][][] bridgeMap) {
        List<List<Integer>> res = new ArrayList<>();
        for (int g = 1; g <= enc.numGraphs; g++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int u = 0; u < enc.mcsVCount; u++) {
                    for (int k = 0; k < enc.mcsVCount; k++) {
                        res.add(Arrays.asList(
                                -reachMap[g][v][u],
                                reachMap[0][v][u],
                                -ccMap[k][v], -ccMap[k][u]));
                    }
                }
            }
        }

        // also, if v does not reach u, and u does not reach v in the MCS, they cannot belong to the same mcs
        // todo: if u doesnt reach v and v doesnt reach u, and there does not exists w s.t. w reach both u and v
        // !r(0, v, u) ^ !r(0, v, u) ^ (!b(w1, v, u) ^ !b(w2, v, u), etc) -> !(cc(k,v) ^ cc(k, u))
        for (int v = 0; v < enc.mcsVCount; v++) {
            for (int u = 0; u < enc.mcsVCount; u++) {
                for (int k = 0; k < enc.mcsVCount; k++) {
                    List<Integer> constrains = new ArrayList<>(Arrays.asList(
                            reachMap[0][v][u], reachMap[0][u][v],
                            -ccMap[k][v], -ccMap[k][u]));
                    for (int w = 0; w < enc.mcsVCount; w++) {
                        constrains.add(bridgeMap[w][v][u]);
                    }
                    res.add(constrains);
                }
            }
        }
        return res;
    }

    public static List<List<Integer>> reachThruConstraint(MaxSatEncoder enc, int[][][] reachMap,
                                                          int[][][][] reachThruMap) {
        List<List<Integer>> res = new ArrayList<>();
        for (int g = 0; g <= enc.numGraphs; g++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int w = 0; w < enc.mcsVCount; w++) {
                    if (w == v) continue;
                    for (int u = 0; u < enc.mcsVCount; u++) {
                        if (u == v || u == w) continue;
                        res.add(Arrays.asList(-reachThruMap[g][v][w][u], reachMap[g][v][w]));
                        res.add(Arrays.asList(-reachThruMap[g][v][w][u], reachMap[g][w][u]));
                        res.add(Arrays.asList(-reachMap[g][v][w], -reachMap[g][w][u], reachThruMap[g][v][w][u]));
                    }
                }
            }
        }
        return res;
    }

    public static List<List<Integer>> reachabilityConstraint(MaxSatEncoder enc, int[][][] reachMap,
                                                             int[][][][] reachThruMap) {
        List<List<Integer>> res = new ArrayList<>();
        for (int g = 0; g <= enc.numGraphs; g++) {
            for (int v = 0; v < enc.mcsVCount; v++) {
                for (int u = 0; u < enc.mcsVCount; u++) {
                    if (u == v) continue;
                    List<Integer> oneConstraint = new ArrayList<>();
                    oneConstraint.add(-reachMap[g][v][u]);
                    for (int w = 0; w < enc.mcsVCount; w++) {
                        if (w == u || w == v) continue;
                        oneConstraint.add(reachThruMap[g][v][w][u]);
                        res.add(Arrays.asList(-reachThruMap[g][v][w][u], reachMap[g][v][u]));
                    }
                    res.add(oneConstraint);
                }
            }
        }
        return res;
    }

    // for constraints -------------------------------------------
    public static List<List<Integer>> connectedConstraint(MaxSatEncoder enc) {
        // if v is in V, then there must exist an edge either from v or to v in the MCS
        List<List<Integer>> constraints = new ArrayList<>();
        // for each v in V, generate clauses f() -> v
        // if for all graphs there exists a vertex w where v is mapped to, v is true
        for (int v = 0; v < enc.vCount; v++) {
            List<Integer> currentVConstraint = new ArrayList<>();
            for (int m = 0; m < enc.metadataList.size(); m++) {
                int add = m * enc.vCFCount;
                for (int u = 0; u < enc.vCount; u++) {
                    currentVConstraint.add(enc.CFVars[0][v][u] + add);
                    currentVConstraint.add(enc.CFVars[0][u][v] + add);
                }
            }
            currentVConstraint.add(-v - 1);
            constraints.add(currentVConstraint);
        }
        return constraints;
    }

    // todo: when do we append 0? haven't appended here
    public static List<List<Integer>> domainConstraint(MaxSatEncoder enc) {
        // compute 3d array to store variable for each f(v, g, w),
        // where v = id of vertex in V to be mapped, g = id of graph, w = id of vertex in Gg
        List<List<Integer>> constraints = new ArrayList<>();
        // for each v in V, generate clauses f() -> v
        // if for all graphs there exists a vertex w where v is mapped to, v is true
        for (int v = 0; v < enc.vCount; v++) {
            for (int g = 0; g < enc.numGraphs; g++) {
                for (int w = 0; w < enc.gVertexSize(g); w++) {
                    constraints.add(Arrays.asList(-enc.domainVars[v][g][w], v+1));
                }
            }
//            List<List<Integer>> constraintsForV = domainConstraintPermute(v, varMap);
//            for (List<Integer> c: constraintsForV) {
//                constraints.add(c.stream().map(x -> -x).collect(Collectors.toList()));
//                constraints.get(constraints.size() - 1).add(v + 1);
//            }
        }


        // for each v in V, generate clauses v -> f()
        // if v is true, there exists a vertex w in all graphs where v is mapped to w
        for (int v = 0; v < enc.vCount; v++) {
            for (int g = 0; g < enc.pgraphs.size(); g++) {
                List<Integer> newConstr = new ArrayList<>();
                for (int w = 0; w < enc.gVertexSize(g); w++) {
                    newConstr.add(enc.domainVars[v][g][w]);
                }
                newConstr.add(-(v + 1));
                constraints.add(newConstr);
            }
        }

        // concat and return
        return constraints;
    }

    public static List<List<Integer>> ontoConstraint(MaxSatEncoder enc) {
        List<List<Integer>> constraints = new ArrayList<>();
        // for each v in V, each g in G, ~f(v, g, w) || ~f(v, g, u)
        // in order words, if w != u in Gg, they cannot be mapped to the same v in V
        for (int v = 0; v < enc.vCount; v++) {
            for (int g = 0; g < enc.pgraphs.size(); g++) {
                for (int w = 0; w < enc.gVertexSize(g); w++) {
                    for (int u = w + 1; u < enc.gVertexSize(g); u++) {
                        constraints.add(Arrays.asList(-enc.domainVars[v][g][w], -enc.domainVars[v][g][u]));
                    }
                }
            }
        }
        return constraints;
    }

    public static List<List<Integer>> oneToOneConstraint(MaxSatEncoder enc) {
        List<List<Integer>> constraints = new ArrayList<>();
        // for each g in G, each w in Gg, ~f(v1, g, w) || ~f(v2, g, w)
        // in order words, if v1 != v2 in V, they cannot be mapped to the same w in Gg
        for (int g = 0; g < enc.numGraphs; g++) {
            for (int w = 0; w < enc.gVertexSize(g); w++) {
                for (int v1 = 0; v1 < enc.vCount; v1++) {
                    for (int v2 = v1 + 1; v2 < enc.vCount; v2++) {
                        constraints.add(Arrays.asList(-enc.domainVars[v1][g][w], -enc.domainVars[v2][g][w]));
                    }
                }
            }
        }
        return constraints;
    }

    // if v is mapped to w in Gg, then type of v in V = type of w in G
    public static List<List<Integer>> typePreserveConstraint(MaxSatEncoder enc) {
        List<List<Integer>> constraints = new ArrayList<>();
        // f(v, g, w) ->  t(t, 0, v) = t(t, g, w) equiv to
        // ~f(v, g, w) or ~t(t, 0, v) or t(t, g, w) AND
        // ~f(v, g, w) or t(t, 0, v) or ~t(t, g, w)
        for (int v = 0; v < enc.vCount; v++) {
            for (int t = 0; t < enc.tacSigCount; t++) {
                for (int g = 0; g < enc.numGraphs; g++) {
                    for (int w = 0; w < enc.gVertexSize(g); w++) {
                        constraints.add(Arrays.asList(
                                -enc.domainVars[v][g][w],
                                -enc.typeVars[t][0][v],
                                enc.typeVars[t][g + 1][w]));
                        constraints.add(Arrays.asList(
                                -enc.domainVars[v][g][w],
                                enc.typeVars[t][0][v],
                                -enc.typeVars[t][g + 1][w]));
                    }
                }
            }
        }
        return constraints;
    }

    // if v1 is mapped to w1 in Gg, v2 is mapped to w2 in Gg, and (v1, v2) is an edge,
    // then (w1, w2) is also an edge in Gg
    public static List<List<Integer>> CFPreserveConstraint(MaxSatEncoder enc) {
        List<List<Integer>> constraints = new ArrayList<>();
        for (int m = 0; m < enc.metadataList.size(); m++) {
            int add = m * enc.vCFCount;
            for (int g = 0; g < enc.numGraphs; g++) {
                for (int v1 = 0; v1 < enc.vCount; v1++) {
                    for (int v2 = 0; v2 < enc.vCount; v2++) {
                        for (int w1 = 0; w1 < enc.gVertexSize(g); w1++) {
                            for (int w2 = 0; w2 < enc.gVertexSize(g); w2++) {
                                constraints.add(Arrays.asList(
                                        -enc.domainVars[v1][g][w1],
                                        -enc.domainVars[v2][g][w2],
                                        -(enc.CFVars[0][v1][v2] + add),
                                        enc.CFVars[g + 1][w1][w2] + add));
                            }
                        }
                    }
                }
            }

        }
        return constraints;
    }

    public static List<List<Integer>> noSpurCFConstraint(MaxSatEncoder enc) {
        // if there exists an edge (v1, v2) in E, then both v1 and v2 are true
        List<List<Integer>> constraints = new ArrayList<>();
        for (int m = 0; m < enc.metadataList.size(); m++) {
            int add = m * enc.vCFCount;
            for (int v1 = 0; v1 < enc.vCount; v1++) {
                for (int v2 = 0; v2 < enc.vCount; v2++) {
                    constraints.add(Arrays.asList(-enc.CFVars[0][v1][v2] - add, v1 + 1));
                    constraints.add(Arrays.asList(-enc.CFVars[0][v1][v2] - add, v2 + 1));
                }
            }

        }
        return constraints.stream().distinct().collect(Collectors.toList());
    }

    public static List<List<Integer>> noDanglingChildConstraint(MaxSatEncoder enc) {
        // for each mapping f(v, g, w), if e(m, u, w) in g, then there exists a mapping from v' to u, and e(m, v', v)
        // f(v, g, w) and e(g, u, w) -> OR_v' (f(v', g, u))
        // ~f(v, g, w) or ~e(g, u, w) or (forall v', f(v', g, u))
        List<List<Integer>> constraints = new ArrayList<>();
        for (int g = 0; g < enc.numGraphs; g++) {
            for (int v = 0; v < enc.vCount; v++) {
                for (int w = 0; w < enc.gVertexSize(g); w++) {
                    for (int u = 0; u < enc.gVertexSize(g); u++) {
                        for (int m = 0; m < enc.metadataList.size(); m++) {
                            int add = m * enc.vCFCount;
                            List<Integer> oneConstraint = new ArrayList<>();
                            oneConstraint.add(-enc.domainVars[v][g][w]);
                            oneConstraint.add(-enc.CFVars[g+1][u][w] - add);
                            for (int v1 = 0; v1 < enc.vCount; v1++) {
                                oneConstraint.add(enc.domainVars[v1][g][u]);
                            }
                            constraints.add(oneConstraint);
                        }
                    }
                }
            }
        }

        return constraints;
    }


    // for io ----------------------------------------------------
    public static void writeTo(String output, String fileName)
            throws IOException {
        File file = new File(fileName);
        file.getParentFile().mkdirs(); // Create parent directories if they don't exist
        BufferedWriter writer = new BufferedWriter(new FileWriter(file));
        writer.write(output);
        writer.close();
    }

    public static List<Integer> getSolutionList(String filename) {
        try (Scanner myReader = new Scanner(new File(filename))) {
            while (myReader.hasNextLine()) {
                String l = myReader.nextLine();
                if (l.startsWith("v")) {
                    return convertOutput(l);
                }
            }
        } catch (FileNotFoundException e) {
            System.out.println("cannot find file");
            e.printStackTrace();
        }
        return null;
    }

    private static List<Integer> convertOutput(String output) {
        // output starts with "v "
        return Arrays.stream(output.split(" "))
                .filter(x -> !x.equals("v"))
                .mapToInt(x -> Integer.parseInt(x))
                .boxed().collect(Collectors.toList());
    }

    public static Map<String, String> gatherCompositeArgs(List<CoqTactic> compTactic) {
        // given a list of atomic tactics in a composite tactic, returns the list of arguments
        List<String> args = new ArrayList<>();
        Map<String, String> res = new LinkedHashMap<>();  // key: arg names, val: "in" or "out"
        for (CoqTactic tactic: compTactic) {
            if (tactic == null) continue;
            // System.out.println("gather args for " + tactic.toCoqScript());
            // add the args for all the tactics
//<<<<<<< HEAD
//            for (CoqTactic.Prop arg: tactic.gatherArgs(tactic.signature).keySet()) {
            for (Map.Entry<String, CoqTactic.Prop> argEnt: tactic.gatherArgs(tactic.signature).entrySet()) {
                CoqTactic.Prop arg = argEnt.getValue();
//            for (CoqTactic.Prop arg: serializeArgs(tactic.gatherArgs(tactic.signature))) {
                if (arg == null) {
                    System.out.println();
                }
                if (args.contains(arg.simpleName())) continue;
                // System.out.println(arg.simpleName());
                String type = argEnt.getKey();
                if (type.contains("in")) {
                    res.put(arg.simpleName(), "_i");
                } else {
                    res.put(arg.simpleName(), "_o");
                }
                args.add(arg.simpleName());
            }
//            Map<CoqTactic.Prop, String> argMap = tactic.gatherArgs();
//            for (CoqTactic.Prop input : tactic.inputs) {
//                String argName = input.simpleName();
//                if (input.type.equals(CoqTactic.PROP_TYPE.GOAL) || args.contains(argName)) continue;
//                args.add(argName);
//            }
//
//            for (CoqTactic.Prop output : tactic.outputs) {
//                String argName = output.simpleName();
//                if (output.type.equals(CoqTactic.PROP_TYPE.GOAL) || args.contains(argName)) continue;
//                args.add(argName);
//            }
//=======
//            List<String> tArgs = new ArrayList<>();
//            tactic.getArgList(tactic.signature, tArgs, new ArrayList<>());
//            args.addAll(tArgs);
//>>>>>>> a78c9fa6352c6253a19657786e6dbf85f3092a1a
        }
        return res;
    }

    public static List<Integer> topoSort(Map<Integer, Integer> indegrees, List<List<Integer>> neighbors) {
        Map<Integer, Integer> branchPriorities = new HashMap<>();
        for (int v = 0; v < indegrees.size(); v++)
            branchPriorities.put(v, 0);

        List<Integer> sources = new ArrayList<>();
        for(Map.Entry<Integer, Integer> entry : indegrees.entrySet()) {
            if (entry.getValue() == 0) {
                sources.add(entry.getKey());
            }
        }

        // initially, no nodes in our ordering
        List<Integer> topologicalOrdering = new ArrayList<>();

        // as long as there are nodes with no incoming edges that can be
        // added to the ordering
        while (!sources.isEmpty()) {

            // add one of those nodes to the ordering
            int u = getMostBranchPrioritized(sources, branchPriorities);
            sources.remove((Integer)u);
//            System.out.println(u + " is the next source");
            topologicalOrdering.add(u);

            // decrement the indegree of that node's neighbors
            for (int v: neighbors.get(u)) {
                indegrees.put(v, indegrees.get(v) - 1);
                branchPriorities.put(v, branchPriorities.get(u) + 1);
                if (indegrees.get(v) == 0) {
                    sources.add(v);
                }
            }
        }

        // we've run out of nodes with no incoming edges
        // did we add all the nodes or find a cycle?
        if (topologicalOrdering.size() != indegrees.size()) {
            throw new IllegalArgumentException("Graph has a cycle! No topological ordering exists.");
        }

        return topologicalOrdering;
    }

    private static int getMostBranchPrioritized(List<Integer> sources, Map<Integer, Integer> branchPriorities) {
        if (sources.size() == 1) return sources.get(0);

        int maxPriority = -1;
        int res = 0;
        for (int v : sources) {
            if (maxPriority < branchPriorities.get(v)) {
                maxPriority = branchPriorities.get(v);
                res = v;
            }
        }
        return res;
    }

    // res[1]: script; res[0]: signature
    public static List<String> tacticsToLtacScript(List<CoqTactic> ltac, String ltacName) {
        // TODO: this doesn't quite work yet b/c it doesn't take goal scopes into account.
        // TODO: track fresh argument
        // It also doesn't track arguments / make fresh results
        Map<String, String> argPosMap = gatherCompositeArgs(ltac);
        String inputArgs = String.join(" ", argPosMap.keySet().stream().toList());
        String res = ltacName + " " + inputArgs + " := ";
//        System.out.println("ltac is " + ltac.size());
        // create a temp arg map
        try {
            res += tacticsToScript(ltac);
        } catch (Exception e) {
            e.printStackTrace();
        }

        String genericSig = ltacName + " " + String.join(" ", argPosMap.values().stream().toList());
//        System.out.println("++++ " + res);
        return Arrays.asList(genericSig, res);
    }

    public static String tacticsToScript(List<CoqTactic> tactics) throws Exception {
        Map<CoqTactic, Integer> insertIndexMap = new HashMap<>();
        String res = "";
        for (int i = 0; i < tactics.size(); i++) {
            // System.out.println("tactic is: " + tactics.get(i).toCoqScript());
            int insertInd = findInsertIndex(res, tactics.get(i), i, tactics, insertIndexMap);
            if (insertInd == -1) {
                // System.out.println("not enough space to insert new tactic " + tactics.get(i).toCoqScript());
                // System.out.println("re-routing");
                res += " .";
                insertInd = res.length() - 1;
            }
//            res += tactics.get(i).toCoqScript();
            int prevResLen = res.length();
            if (insertInd == -2)
                System.out.println();
            res = insertTactic(res, insertInd, tactics.get(i), insertIndexMap);
//            int insertLen = res.length() - prevResLen;

            // for any index that comes = or after the insertIndex, bump them up by insertLen.
//            for (Map.Entry<CoqTactic, Integer> entry: insertIndexMap.entrySet()) {
//                if (insertInd <= entry.getValue()) {
//                    insertIndexMap.put(entry.getKey(), entry.getValue() + insertLen);
//                }
//            }
//            insertIndexMap.put(tactics.get(i), insertInd);
            // System.out.println("res after inserting " + i + ": " + res);
        }

        // System.out.println("result is " + res);
        while (res.indexOf("; [ | .. ]") != -1) {
            res = res.replace("; [ | .. ]", "");
        }
        while (res.indexOf("; [ |  | .. ]") != -1) {
            res = res.replace("; [ |  | .. ]", "");
        }
        while (res.indexOf("; []") != -1) {
            res = res.replace("; []", "");
        }
        while (res.indexOf("]]") != -1) {
            res = res.replace("]]", "] | .. ]");
        }
        while (res.indexOf("|  | .. ]") != -1) {
            res = res.replace("|  | .. ]", "| .. ]");
        }

        // System.out.println("returning result of " + res);
        return res;
    }

    /**
     * @param script: the script to insert next tactic
     * @return the index where to insert the tactic
     */
    private static int findInsertIndex(String script, CoqTactic tactic, int currIndex, List<CoqTactic> tactics, Map<CoqTactic, Integer> insertIndexMap) {
        // todo: more complex than this, basically it needs to know which goal branch it belongs to
        if (script.equals(".")) return 0;

        CoqTactic.Prop inputGoalProp = null;
        for (CoqTactic.Prop in: tactic.inputs) {
            if (in.type.equals(CoqTactic.PROP_TYPE.GOAL)) {
                inputGoalProp = in;
                break;
            }
        }

        // if it only depends on hyp, find the goal branch the dependent hyp is on, and find the last index of that goal branch
        if (inputGoalProp == null) {
            CoqTactic parentTactic = null;
            int branchID = 0;
            for (int i = currIndex - 1; i >= 0; i--) {
                CoqTactic parentCandidate = tactics.get(i);
                for (CoqTactic.Prop parentOut: parentCandidate.outputs) {
                    if (tactic.inputs.contains(parentOut)) {
                        parentTactic = parentCandidate;
                        break;
                    } else if (parentOut.type.equals(CoqTactic.PROP_TYPE.GOAL)) {
                        branchID++;
                    }
                }
                if (parentTactic != null) break;
                branchID = 0;
            }
            int index = insertIndexMap.getOrDefault(parentTactic, 0);
            String relevantScript = script.substring(index);
            // from after the parent tactic, do the following
            if (branchID < 2) {
                if (relevantScript.indexOf("[ |") != -1) return relevantScript.indexOf("[ |") + index + 1;
                if (relevantScript.indexOf("[]") != -1) return relevantScript.indexOf("[]") + index + 1;
                if (relevantScript.indexOf("|  |") != -1) return relevantScript.indexOf("|  |") + index + 2;
//                if (script.indexOf("[]") != -1) return script.indexOf("[]") + 1;
            } else {
                // if branch ID >= 2, we need to find the ID'th bar of the level of the current tactic
                String copy = new String(relevantScript);
                while (copy.indexOf("|  |") != -1) {
                    int ind = copy.indexOf("|  |");
                    int open = 0;
                    for (int i = 0; i < ind; i++) {
                        char c = copy.charAt(i);
                        if (c == '[') open++;
                        else if (c == ']') open--;
                    }
                    if (open > 1) copy = copy.replaceFirst("\\|  \\|", "****");
                    else return ind + index + 2;
                }
//               if (relevantScript.indexOf("|  |") != -1) return relevantScript.indexOf("|  |") + index + 2;
            }
        }

        // if it depends on a goal of a tactic, find on which goal branch of it depends on
        int numSkips = 0;
        for (int i = currIndex - 1; i >=0; i--) {
            CoqTactic parentCandidate = tactics.get(i);
//            if (parentCandidate.equals(tactic)) continue;

//            int branch = parentCandidate.outputs.stream().filter(o -> o.type.equals(CoqTactic.PROP_TYPE.GOAL))
//                    .collect(Collectors.toList()).size();
            int branch = 0;
            for (CoqTactic.Prop parentIn: parentCandidate.inputs) {
                if (parentIn.type.equals(CoqTactic.PROP_TYPE.HYP)) continue;
                if (parentIn.equals(inputGoalProp)) {
                    // curr goal is transformed, so the most recent parent is not the actual parent
                    if (!parentCandidate.outputs.contains(inputGoalProp)) {
                        numSkips++;
                    }
                    break;
                }
            }

            for (CoqTactic.Prop parentOut: parentCandidate.outputs) {
                if (parentOut.type.equals(CoqTactic.PROP_TYPE.HYP)) continue;

//                branch--;
                branch++;
                if (parentOut.equals(inputGoalProp)) {
                    if (numSkips > 0) {
                        numSkips--;
                        break;
                    }

                    // find the branch-th slot
                    int parentIndex = insertIndexMap.get(parentCandidate);
//                    if (branch == 1 && script.indexOf("[]") != -1) return script.indexOf("[]") + 1;
                    int insertInd = findNthPipeIndex(script, parentCandidate.toCoqScript(), parentIndex, tactic.toCoqScript(), branch) - 1;
                    if (script.substring(0, insertInd).endsWith("; []")) insertInd--;
                    return insertInd;
                }
            }
        }

        if (script.indexOf("[]") != -1) return script.indexOf("[]") + 1;
        return -1;
    }

    private static int findNthPipeIndex(String input, String afterPattern, int startIndex, String tactic, int n) {
        // System.out.println(tactic + " is child of " + afterPattern + ", branch " + n);
        // find the most recent indexOfAfter
//        String updatedInput = input;
        int indexOfAfter = startIndex + afterPattern.length(); //input.indexOf(afterPattern) + afterPattern.length();
//        while (updatedInput.indexOf(afterPattern) != -1) {
//            int tempIndex = updatedInput.indexOf(afterPattern) + afterPattern.length();
//            indexOfAfter += tempIndex;
//            updatedInput = updatedInput.substring(tempIndex);
//        }

        String inputSubstring = input.substring(indexOfAfter);
        int count = 0;
        int bracketCount = -1;
        for (int i = 0; i < inputSubstring.length(); i++) {
            if (inputSubstring.charAt(i) == '|') {
                if (bracketCount == 0)
                    count++;
                if (count == n) {
                    return i + indexOfAfter;
                }
            } else if (inputSubstring.charAt(i) == '[') {
                bracketCount++;
            } else if (inputSubstring.charAt(i) == ']') {
                bracketCount--;
            }
        }
        return -1; // Return -1 if the n-th pipe is not found
    }

    // insert tactic at index ind on script
    private static String insertTactic(String script, int ind, CoqTactic tactic, Map<CoqTactic, Integer> insertIndMap) {
        String before = script.substring(0, ind);
        String after = script.substring(ind);
        if (before.endsWith("]")) {
            int n = before.length() - 1;
            String pre = "";
            while (n >= 0) {
                if (before.charAt(n--) == ']')
                    pre += ']';
                else
                    break;
            }
            before = before.substring(0, before.length() - pre.length());
            after = pre + after;
        }
        StringBuilder sb = new StringBuilder(before)
                .append(tactic.toCoqScript());

        // append suffix
        if (!tactic.outputs.isEmpty()) {
            sb.append("; [");
            // find how many bars to insert
            List<CoqTactic.Prop> outputGoals = tactic.outputs.stream()
                    .filter(o -> o.type.equals(CoqTactic.PROP_TYPE.GOAL))
                    .collect(Collectors.toList());
            // if there is no goal outputted, put none
            if (!outputGoals.isEmpty()) {
                // if there are n goals, put n bars, and append ".." after the last bar
                for (CoqTactic.Prop p: outputGoals) {
                    sb.append(" | ");
                }
                sb.append(".. ");
            }
            sb.append("]");
        }

        sb.append(after);

        int insertLen = sb.length() - script.length();
        int insertInd = before.length() + 1;

        for (Map.Entry<CoqTactic, Integer> entry: insertIndMap.entrySet()) {
            if (insertInd <= entry.getValue()) {
                insertIndMap.put(entry.getKey(), entry.getValue() + insertLen);
            }
        }
        insertIndMap.put(tactic, before.length() + 1);
        return sb.toString();
    }

    // Returns the set of valid custom tactics (as corresponding booleans)
    public static List<Boolean> retrieveValidCustomTactics(List<CoqProof> customTactics, String vFile) throws IOException {
        
        /* temporary */
        List<Boolean> temp = new ArrayList<>();
        for(CoqProof each: customTactics) {
            temp.add(true);
        }
        return temp;

        // StringBuilder allTactics = new StringBuilder("");
        // for (CoqProof each: customTactics) allTactics.append(each.raw_string + "\n");
        // // Write candidate tactics to file
        // writeTo(vFile + "\n" + allTactics.toString(), Paths.maxsatFilesPath + "tacticList.txt");
        // try {
        //     // Use python script to verify tactics
        //     ProcessBuilder processBuilder = new ProcessBuilder("python3", "src/python/tactic_validity_check.py");
        //     processBuilder.directory(new File(System.getProperty("user.dir")));
        //     Process process = processBuilder.start();
        //     int exitCode = process.waitFor();
        // } catch (IOException | InterruptedException e) {
        //     e.printStackTrace();
        // }

        // // Read in successful tactics
        // List<Boolean> validTactics = new ArrayList<>();
        // try (BufferedReader br = new BufferedReader(new FileReader(Paths.maxsatFilesPath + "tacticList_verified.txt"))) {
        //     String line;
        //     boolean noSolsFlag = true;
        //     while ((line = br.readLine()) != null) {
        //         if (line.equals("T")) {
        //             validTactics.add(true);
        //             noSolsFlag = false;
        //         } else {
        //             validTactics.add(false);
        //         }
        //     }

        //     if (noSolsFlag) System.out.println("No valid tactics found :(");

        // } catch (IOException e) {
        //     e.printStackTrace();
        // }

        // return validTactics;
    }

    // todo: returns true if contractedProofs can be accepted by coq
    /*
     @contractedProofs: list of (sampled) contracted proofs with our custom tactics
     @filename: the filename of the original coq proof scripts (contains all the the proofs instead of just the sampled ones)
     @proofIDs: the id's of each contracted proof in the list (their id corresponds to their order in the original proof script)
     */
    public static String isContractedProofValid(List<String> lemmaNames, List<String> contractedProofs, MaxSatEncoder mse, String vFile, String outFile) throws IOException {
        // write to resources
        StringBuilder sb = new StringBuilder("");
        for (int i = 0; i < lemmaNames.size(); i++) {
            sb.append(lemmaNames.get(i)); sb.append('\n');
            sb.append(contractedProofs.get(i)); sb.append('\n');
        }
        String contractedScript = sb.toString();

        return contractedScript; // temporary

        // System.out.println(contractedScript);
        // System.out.println(mse.customTacticScripts);
        // System.out.println(mse.validCustomTactics);

        // StringBuilder allTactics = new StringBuilder("");
        // for (int i = 0; i < mse.customTacticScripts.size(); i++) {
        //     if (mse.validCustomTactics.get(i)) {
        //         allTactics.append(mse.customTacticScripts.get(i));
        //         allTactics.append('\n');
        //     }
        // }
        // // Write valid tactics to file
        // writeTo(vFile + "\n-----\n" + outFile + "\n-----\n" + allTactics.toString() + "-----\n" + contractedScript, Paths.maxsatFilesPath + "tacticList.txt");

        // try {
        //     // Use python script to verify proofs
        //     ProcessBuilder processBuilder = new ProcessBuilder("python3", "src/python/proof_validity_check.py");
        //     processBuilder.directory(new File(System.getProperty("user.dir")));
        //     Process process = processBuilder.start();
        //     int exitCode = process.waitFor();
        // } catch (IOException | InterruptedException e) {
        //     e.printStackTrace();
        // }

        // // Read in successful proofs
        // boolean valid = false;
        // try (BufferedReader br = new BufferedReader(new FileReader(Paths.maxsatFilesPath + "tacticList_verified.txt"))) {
        //     String line;
        //     if ((line = br.readLine()) != null) {
        //         if (line.equals("T")) {
        //             valid = true;
        //         }
        //     }
        // } catch (IOException e) {
        //     e.printStackTrace();
        // }

        // return valid ? contractedScript : null;
    }
}
