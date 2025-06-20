package main.maxsat;

import main.config.BmConfig;
import main.encode.*;
import main.proofgraph.ProofGraph;

import static main.maxsat.MaxSATDebugger.*;
import static main.maxsat.MaxSATUtil.*;

import java.io.*;
import java.util.*;
import java.util.stream.*;

public class MaxSatEncoder {
    // Store all proof dependency graphs
    int numGraphs;
    public List<CoqProof> pgraphs;

    // Store all tactic signatures and mappings
    List<String> tacticList;
    public List<List<Integer>> connCompMcsIDs = new ArrayList<>(); // starting with 1
    public List<CoqProof> customTacticScripts = new ArrayList<>();
    public List<Boolean> validCustomTactics;
    Map<String, Integer> vTypeMap;

    List<ProofGraph.Edge> metadataList; // Encodes edge "types", where type = (from, to) in u.from --> v.to
    int tacSigCount = 0;   // for stat purposes
    int maxNumNodes = 0;   // for stat purposes
    int minNumNodes = Integer.MAX_VALUE;   // for stat purposes

    // MaxSAT variable counts
    public int vCount;
    int vDomainCount;
    int vTypeCount;
    int vCFCount;
    int vCFMetaCount;

    // Solutions
    int mcsVCount;
    List<Integer> mcsVertices = new ArrayList<>();
    List<Integer> mcsSol;
    List<Integer> updatedSol;

    int[][][] domainVars;
    int[][][] typeVars;
    int[][][] CFVars;

    Map<String, Integer> argMap = new HashMap<>();
    int numLtacs = 0;

    public MaxSatEncoder(List<CoqProof> pgraphs) {
        this.pgraphs = pgraphs;
        this.numGraphs = this.pgraphs.size();
        init();
    }

    // -------------------
    // Initialization
    // -------------------

    public void init() {
        this.metadataList = getMetadata();
        initVertexTypeMap();
        initCount();
        initVariableMaps();
    }

    // Encodes edge "types", where type = (from, to) in u.from --> v.to
    public List<ProofGraph.Edge> getMetadata() {
        Set<ProofGraph.Edge> metadataSet = new HashSet<>();
        for (CoqProof pgraph: this.pgraphs) {
            for (List<ProofGraph.Edge> each: pgraph.pgraph.adjList) {
                for (ProofGraph.Edge edge : each) {
                    metadataSet.add(new ProofGraph.Edge(-1, -1, edge.fromPos, edge.toPos));
                }
            }
        }
        return metadataSet.stream().toList();
    }

    public List<String> initVertexTypeMap() {
        // Extract the finite set of distinct tactic signatures from all proofs
        this.vTypeMap = new HashMap<>();
        for (CoqProof pgraph : this.pgraphs) {
            for (CoqTactic tactic : pgraph.pgraph.vertices) {
                this.vTypeMap.put(tactic.sig_no_out_arg, Integer.MAX_VALUE);
            }
        }
        this.tacticList = this.vTypeMap.keySet().stream().toList();
        this.tacSigCount = this.tacticList.size();

        // Compute counts from each proof graph and bound the MCS counts
        // Currently enabled; need to confirm if this is expected behavior
        for (CoqProof pg : this.pgraphs) {
            Map<String, Integer> oneVTypeMap = countOnePGVertex(pg.pgraph);
            for (String sig : oneVTypeMap.keySet()) {
                // if for type t, count(t) < vTypeMap[t], update vTypeMap
                this.vTypeMap.put(sig, Math.min(oneVTypeMap.get(sig), this.vTypeMap.get(sig)));
            }
        }
        return this.tacticList;
    }

    public void initCount() {
        // max number of vertices in the MCS
        this.vCount = this.vTypeMap.values().stream().reduce(0, Integer::sum);

        // mapping from vertices in common subgraph to each input graph
        // for each v in V, each u in Gi, fi(v, u) denotes
        // if v in G is mapped to u in Gi (free variables)
        // sum_i(vCount * |Vi|)
        this.vDomainCount = this.vCount *
                                this.pgraphs.stream().map(pg -> pg.pgraph.vertices.size())
                                        .reduce(0, Integer::sum);

        // denote the possible type mappings for each node
        // for each v in V or Vi, and r in T(type set for tactic types),
        // ti(v, r) denotes if v is of type r (free in V, constant in Vi)
        // typeCount * vCount + sum_i(typeCount * Vi)
        this.vTypeCount = this.tacSigCount * 
                            this.pgraphs.stream().map(pg -> pg.pgraph.vertices.size())
                            .reduce(this.vCount, Integer::sum);

        // denote the number of possible edges
        // for each v, u in V or Vi, ei(v, u) denotes
        // if there is an edge (v, u) in Ei (free in V, constant in Vi)
        // vCount * vCount + sum(|Vi| * |Vi|)
        this.vCFCount = this.pgraphs.stream()
                            .map(pg -> pg.pgraph.vertices.size())
                            .map(vc -> vc * vc)
                            .reduce(this.vCount * this.vCount, Integer::sum);

        // denote the number of possible edges with distinct source/sink position indices
        // for every v, u in V or Vi, yi(v, u, d) indicates
        // whether there is metadata (v, u, d) in Yi  (free in V, constant in Vi)
        // |indicators| * |metadataSet|
        this.vCFMetaCount = this.metadataList.size() * this.vCFCount;
    }

    public void initVariableMaps() {
        this.domainVars = computeDomainVars();
        this.typeVars = computeTypeVars();
        this.CFVars = computeCFVars();
    }

    public void addAtomClauses(List<String> res, int weight, List<Integer> clauses) {
        res.addAll(clauses.stream()
                .map(ind -> Integer.toString(ind))
                .map(s -> weight + " " + s + " 0")
                .collect(Collectors.toList()));
    }
    
    public void addLongClauses(List<String> res, int weight, List<List<Integer>> clauses) {
        res.addAll(clauses.stream()
                .map(l -> l.stream().map(String::valueOf).collect(Collectors.joining(" ")))
                .map(s -> weight + " " + s + " 0")
                .collect(Collectors.toList()));
    }

    // -------------------
    // Encoding, Round 1
    // -------------------

    public String encodeSAT(boolean printStat) {
        List<String> output = new ArrayList<>();
        // for all d(v), put a soft clause down
        int softWeight = 1;
        addObjectiveConstraints(output, softWeight);

        int maxWeight = softWeight * output.size() + 1;
        addConstants(output, maxWeight);
        addConstraints(output, maxWeight);

        // first line
        int numVars = this.vCount + this.vDomainCount + this.vTypeCount + this.vCFMetaCount;
        int numClause = output.size();
        String outStr = output.stream().map(String::valueOf).collect(Collectors.joining("\n"));
        String firstLine = "p wcnf " + numVars + " " + numClause + " " + maxWeight + "\n";
        if (printStat) {
            printCounts();
            printStat();
        }

        return firstLine + outStr;
    }

    public String encodeSATAllCommonGraphs(boolean printStat, List<List<Integer>> solutionBan) {
        List<String> output = new ArrayList<>();
        // for all d(v), put a soft clause down
        int weight = 1;
        addObjectiveAllCommonGraphs(output, weight);

        addConstants(output, weight);
        addConstraints(output, weight);

        addSolutionBan(output, weight, solutionBan);

        // first line
        int numVars = this.vCount + this.vDomainCount + this.vTypeCount + this.vCFMetaCount;
        int numClause = output.size();
        String outStr = output.stream().map(String::valueOf).collect(Collectors.joining("\n"));
        String firstLine = "p wcnf " + numVars + " " + numClause + "\n";
        if (printStat) {
            printCounts();
            printStat();
        }

        return firstLine + outStr;
    }

    public void addConstants(List<String> output, int weight) {
        // all constant type + CF indicators
        addAtomClauses(output, weight, constantTypeInd());
        addAtomClauses(output, weight, constantCFInd());
    }

    public void addConstraints(List<String> output, int weight) {
        // add all constraints
        addLongClauses(output, weight, domainConstraint(this));
        addLongClauses(output, weight, ontoConstraint(this));
        addLongClauses(output, weight, oneToOneConstraint(this));
        addLongClauses(output, weight, typePreserveConstraint(this));
        addLongClauses(output, weight, CFPreserveConstraint(this));
        addLongClauses(output, weight, noSpurCFConstraint(this));
    }

    public void addSolutionBan(List<String> output, int weight, List<List<Integer>> solutionBan) {
        // negate each list of the solution ban
        addLongClauses(output, weight, solutionBan);
    }

    // ------------------------ helper functions for generating constraints
    /*
     returns a list of list, where L(i) stores the i-th clause variable
     constraints about vertex mapping
     # of clauses: Π_i|Vi|, where Vi is the vertex set of each Gi
     length of each clause: |G| + 1

     @v: the id of the vertex v in V (the vertex to be mapped)
     */

    public int[][][] computeDomainVars() {
        // count maxVSize to define array dimension
        int maxVSize = this.maxGraphSize();
        int[][][] res = new int[vCount][this.numGraphs][maxVSize];
        int var = this.vCount + 1;
        for (int v = 0; v < this.vCount; v++) {
            for (int g = 0; g < this.numGraphs; g++) {
                for (int w = 0; w < gVertexSize(g); w++) {
                    res[v][g][w] = var;
                    var++;
                }
            }
        }
        return res;
    }

    public int[][][] computeTypeVars() {
        // int[num-tactics][num-graphs][num-vertices-in-Gg]
        int[][][] res = new int[this.tacSigCount][this.numGraphs + 1][this.maxGraphSize()];
        int var = this.vCount + this.vDomainCount + 1;
        for (int t = 0; t < this.tacSigCount; t++) {
            for (int v = 0; v < this.vCount; v++) {
                res[t][0][v] = var;
                var++;
            }
            for (int g = 0; g < this.numGraphs; g++) {
                for (int w = 0; w < gVertexSize(g); w++) {
                    res[t][g+1][w] = var;
                    var++;
                }
            }
        }
        return res;
    }

    public int[][][] computeCFVars() {
        // int[g][from][to]
        int maxVSize = this.maxGraphSize();
        int[][][] res = new int[numGraphs + 1][maxVSize][maxVSize];
        int var = this.vCount + this.vDomainCount + this.vTypeCount + 1;
        for (int v1 = 0; v1 < this.vCount; v1++) {
            for (int v2 = 0; v2 < this.vCount; v2++) {
                res[0][v1][v2] = var++;
            }
        }

        for (int g = 0; g < this.numGraphs; g++) {
            for (int w1 = 0; w1 < gVertexSize(g); w1++) {
                for (int w2 = 0; w2 < gVertexSize(g); w2++) {
                    res[g + 1][w1][w2] = var++;
                }
            }
        }
        return res;
    }

    public void addObjectiveAllCommonGraphs(List<String> res, int weight) {
        // at long as one common edge exists
        List<String> oneConstraint = new ArrayList<>();
        for (int v = 0; v < this.vCount; v++) {
            for (int u = 0; u < this.vCount; u++) {
                for (int m = 0; m < this.metadataList.size(); m++) {
                    int add = m * this.vCFCount;
                    oneConstraint.add("" + (CFVars[0][v][u] + add));
                }
            }
        }
        res.add(weight + " " + String.join(" ", oneConstraint) + " 0");
    }

    public void addObjectiveConstraints(List<String> res, int weight) {
        for (int v = 0; v < this.vCount; v++) {
            for (int u = 0; u < this.vCount; u++) {
                List<String> oneConstraint = new ArrayList<>();
                for (int m = 0; m < this.metadataList.size(); m++) {
                    int add = m * this.vCFCount;
                    oneConstraint.add("" + (CFVars[0][v][u] + add));
                }
                res.add(weight + " " + String.join(" ", oneConstraint) + " 0");
            }
        }
    }

    // output the type indicator constraint
    public List<Integer> constantTypeInd() {
        Set<Integer> trueVar = new HashSet<>();
        Set<Integer> freeVar = new HashSet<>();
        for (int t = 0; t < this.tacticList.size(); t++) {
            // constant for the subgraph
            for (int v = 0; v < this.vCount; v++)
                freeVar.add(typeVars[t][0][v]);

            String tacSig = this.tacticList.get(t);
            // constant for each graph in pgraphs
            for (int g = 0; g < this.numGraphs; g++) {
                List<CoqTactic> vertices = this.pgraphs.get(g).pgraph.vertices;
                // if v_k in Gj is of type i, (i - 1) * (total-vertices) + n + sum(|V_{j-1}|)
                for (int w = 0; w < vertices.size(); w++) {
                    if (vertices.get(w).sig_no_out_arg.equals(tacSig))
                        trueVar.add(typeVars[t][g + 1][w]);
                }
            }
        }
        return IntStream.range(typeVars[0][0][0], typeVars[0][0][0] + this.vTypeCount)
                .filter(t -> !freeVar.contains(t))
                .map(t -> (trueVar.contains(t)) ? t : -t)
                .boxed().collect(Collectors.toList());
    }

    // output control-flow constant indicators
    public List<Integer> constantCFInd() {
        Set<Integer> trueVar = new HashSet<>();
        for (int g = 0; g < this.numGraphs; g++) {
            List<List<ProofGraph.Edge>> adjList = this.pgraphs.get(g).pgraph.adjList;
            int numVertices = this.pgraphs.get(g).pgraph.vertices.size();
            
            // Process edges in this proof graph
            for (int from = 0; from < numVertices; from++) {
                // Process edges from <from>
                for (ProofGraph.Edge edge : adjList.get(from)) {
                    int CFVar = CFVars[g + 1][edge.u][edge.v];
                    int metaIndex = this.metadataList.indexOf(new ProofGraph.Edge(-1, -1, edge.fromPos, edge.toPos));
                    trueVar.add(CFVar + metaIndex * this.vCFCount);
                }
            }
        }

        Set<Integer> freeVar = new HashSet<>();
        for (int m = 0; m < this.metadataList.size(); m++) {
            int add = m * this.vCFCount;
            for (int v1 = 0; v1 < this.vCount; v1++) {
                int finalV1 = v1;
                freeVar.addAll(IntStream.range(0, this.vCount)
                       .map(v2 -> CFVars[0][finalV1][v2] + add)
                       .boxed().collect(Collectors.toList()));
            }
        }

        return IntStream.range(CFVars[0][0][0], CFVars[0][0][0] + this.vCFMetaCount)
                .filter(t -> !freeVar.contains(t))
                .map(t -> (trueVar.contains(t)) ? t : -t)
                .boxed().collect(Collectors.toList());
    }


    // -------------------
    // Encoding, Round 2
    // -------------------

    public String encodeSATRd2(List<Integer> solution) throws IOException {
        this.mcsSol = solution;
        this.mcsVertices = this.mcsSol.stream().filter(x -> x <= this.vCount).collect(Collectors.toList());
        System.out.println("mcs vertices: " + this.mcsVertices);
        this.mcsVCount = mcsVertices.size();

        // get maxSAT input
        List<String> output = new ArrayList<>();

        // get reachability matrix
        int[][] ccMap = getCCMap(this);
        int[][][] reachMap = getReachMap(this);
        int[][][][] reachThruMap = getReachThruMap(this);
        int[][] mcsVarMap = getMappingFromMCS(this, this.mcsVertices, this.mcsSol);
        int[][][] bridgeMap = getBridgeMap(this);

        int softWeight = 1;
        // objective
        addSecondObjectives(this, output, softWeight);

        // constants
        int maxWeight = softWeight * output.size() + 1;
        addLongClauses(output, maxWeight, 
                        getReachableConstants(this, reachMap, reachThruMap, mcsVarMap, this.mcsVertices, this.mcsSol));

        // constraints
        addLongClauses(output, maxWeight, ccExistenceConstraint(this, ccMap));
        addLongClauses(output, maxWeight, allVertexMappedConstraint(this, ccMap));
        addLongClauses(output, maxWeight, pathReachabilityConstraint(this, ccMap, reachMap, bridgeMap));
        addLongClauses(output, maxWeight, reachThruConstraint(this, reachMap, reachThruMap));
        addLongClauses(output, maxWeight, additionalReachableConstraint(this, reachMap, reachThruMap));
        addLongClauses(output, maxWeight, bridgeConstraint(this, reachMap, bridgeMap));

        int numVars = reachThruMap[numGraphs][mcsVCount-1][mcsVCount-1][mcsVCount-1];
        int numClause = output.size();
        String outStr = output.stream().map(String::valueOf).collect(Collectors.joining("\n"));
        String firstLine = "p wcnf " + numVars + " " + numClause + " " + maxWeight + "\n";

        return firstLine + outStr;
    }

    private List<List<Integer>> getConnComps() throws IOException {
//        printMappingInfo(this.mcsSol);
        List<List<Integer>> satOut = new ArrayList<>();
        // turn result into res[cc][v-id]
        int[][] ccMap = getCCMap(this);
        for (int v = 0; v < mcsVertices.size(); v++) {
            System.out.println(v + ": " + this.getMCSTypeMap().get(mcsVertices.get(v)));
        }
        for (int k = 0; k < this.mcsVCount; k++) {
            List<Integer> CCk = new ArrayList<>();
            for (int v = 0; v < this.mcsVCount; v++) {
                if (updatedSol.contains(ccMap[k][v])) {
                    // vertex[v] is in cc_k
//                    System.out.println(ccMap[k][v] + ": " +
//                            mcsVertices.get(v) + "-" +this.getMCSTypeMap().get(mcsVertices.get(v)) + " is in CC " + k);
//                    System.out.println("v is " + v + ", cc[1][v]: " + ccMap[1][v]);

                    CCk.add(mcsVertices.get(v));
                }
            }
            satOut.add(CCk);
        }
//        System.out.println("satout: " + satOut);

        List<List<Integer>> res = new ArrayList<>();

        for(List<Integer> candidate: satOut) {
            // First build an undirected graph out of the candidate tactic
            Map<Integer, Set<Integer>> neighbors = new HashMap<>();
            for (int i = 0; i < candidate.size(); i++) {
                neighbors.put(i, new HashSet<>());
            }

            for (int i = 0; i < candidate.size(); i++) {
                for (int j = 0; j < candidate.size(); j++) {
                    int w = candidate.get(i);
                    int v = candidate.get(j);

                    for (int m = 0; m < this.metadataList.size(); m++) {
                        int add = m * this.vCFCount;
                        if (this.mcsSol.contains(this.CFVars[0][v-1][w-1] + add)) {
                            neighbors.get(i).add(j);
                            neighbors.get(j).add(i);
                            break;
                        }
                    }
                }
            }

            // Perform a series of DFS's to extract connected components
            boolean[] visited = new boolean[candidate.size()];
            for (int i = 0; i < candidate.size(); i++) {
                if (!visited[i]) {
                    List<Integer> component = new ArrayList<>();

                    // DFS
                    Stack<Integer> stack = new Stack<>();
                    stack.push(i);
                    while(stack.size() > 0) {
                        int idx = stack.pop();
                        if (visited[idx]) continue;
                        visited[idx] = true;
                        component.add(candidate.get(idx));
                        for (int each: neighbors.get(idx)) {
                            if (!visited[each]) stack.push(each);
                        }
                    }

                    res.add(component);
                }
            }
        }

        // if size of connComp == 1, then check if it's a composite, otherwise remove

        return res.stream().filter(l -> isCCComposite(l)).collect(Collectors.toList());
    }

    private boolean isCCComposite(List<Integer> connComp) {
//        System.out.println("checking connComp: " + connComp);
//        System.out.println("tacLst: " + this.tacticList);
        if (connComp.size() > 1) return true;
//        if (connComp.isEmpty()) return false;
//
//        for (int t = 0; t < this.typeVars.length; t++) {
//            if (this.mcsSol.contains(typeVars[t][0][connComp.get(0) - 1])) {
//                System.out.println("tac of this type: " + this.tacticList.get(t));
//                return (this.tacticList.get(t).contains(";"));
//            }
//        }
        return false;
    }

    // @solution: the entire list of integers read from maxSAT
    public List<CoqProof> maxSATSolToTactics(List<Integer> solution, BmConfig config) throws IOException {
        this.updatedSol = solution;

        // find all connected components
        this.connCompMcsIDs = getConnComps();

        // for each connComp, recover the list of sorted tactics
        for (List<Integer> connComp: connCompMcsIDs) {
            System.out.println(connComp);
            CoqProof customTac = recoverTactics(connComp);
            this.customTacticScripts.add(customTac);
        }

        this.validCustomTactics = retrieveValidCustomTactics(this.customTacticScripts, config.getInputFilename());
        if (this.customTacticScripts.size() != this.validCustomTactics.size()) System.err.println("Error: custom tactic verification array has inconsistent size");

//        System.out.println("Custom tactics:");
        for (int i = 0; i < this.customTacticScripts.size(); i++) {
            if (this.validCustomTactics.get(i)) {
//                System.out.println(this.customTacticScripts.get(i).raw_string);
            } else {
                System.out.println("INVALID TACTIC - " + this.customTacticScripts.get(i));
            }
        }
        System.out.println("\n");

        return this.customTacticScripts;
    }

    protected Map<Integer, String> getGraphTypeMap(int g) {
        Map<Integer, String> map = new HashMap<>();
        for (int w = 0; w < gVertexSize(g); w++) {
            for (int t = 0; t < this.tacticList.size(); t++) {
                if (this.mcsSol.contains(this.typeVars[t][g + 1][w])) {
                    map.put(w, this.tacticList.get(t));
                    break;
                }
            }
        }

        for (Map.Entry<Integer, String> enc: map.entrySet()) {
            System.out.println("in graph " + (g + 1) + ", " + enc.getKey() + " type: " + enc.getValue());
        }
        return map;
    }

    // given a list of integers representing the maxSAT solution,
    // output the corresponding ProofGraph
    protected Map<Integer, String> getMCSTypeMap() {
        Map<Integer, String> map = new HashMap<>();
        Iterator<Integer> nextV = this.mcsSol.listIterator();
        while (nextV.hasNext()) {
            int v = nextV.next();
            if (v > this.vCount) break;

            for (int t = 0; t < this.tacticList.size(); t++) {
                if (this.mcsSol.contains(this.typeVars[t][0][v - 1])) {
                    map.put(v, this.tacticList.get(t));
                    break;
                }

            }

        }
        for (Map.Entry<Integer, String> enc: map.entrySet()) {
            System.out.println(enc.getKey() + " type: " + enc.getValue());
        }

        return map;
    }

    // Recovers a tactic from a MaxSAT solution. The tactic will use the specific inputs/outputs of the graph with id=0
    private CoqProof recoverTactics(List<Integer> vertices) {
        // todo: order of branches needs to match original, which is flipped
        // pass in the tacToScript within this function, but also pass in the fresh args
        List<Integer> sortedVertices = sortedVertices(vertices);
        Map<String, String> argReplace = new HashMap<>();
        int g = 0; // the graph to find the tactic

        // for each sorted vertex convert it to tactic
        // debugging purposes ---------------------------------
//         Map<Integer, String> typeMap = getMCSTypeMap();
//         for (int gr = 0; gr < this.numGraphs; gr++) {
//             Map<Integer, String> gTypeMap = getGraphTypeMap(gr);
//             for (int v : sortedVertices) {
//                 for (int w = 0; w < gVertexSize(gr); w++) {
//                     if (this.mcsSol.contains(this.domainVars[v - 1][gr][w])) {
//                         System.out.println("In graph " + (gr + 1) + ": " + v  + "(" +
//                                 typeMap.get(v) + ") is mapped to " + w +
//                                 " of type " + gTypeMap.get(w));

// //                        System.out.println(this.tacticList.indexOf(gTypeMap.get(w)));
// //                        System.out.println("typeVars[current t][0][v]: "
// //                                + this.typeVars[this.tacticList.indexOf(gTypeMap.get(w))][0][v - 1]);
// //                        System.out.println("typeVars[current t][+" + (gr + 1) +"][w]: "
// //                                + this.typeVars[this.tacticList.indexOf(gTypeMap.get(w))][gr + 1][w]);
//                     }
//                 }
//             }
//         }
        // ------------------------------------------------------

        // TODO: this is outdated, need to think about how to fix

        List<CoqTactic> tactics = new ArrayList<>();
        int id = 0;
        for (int v : sortedVertices) {
            for (int w = 0; w < gVertexSize(g); w++) {
                if (this.mcsSol.contains(this.domainVars[v-1][g][w])) {
                    CoqTactic nTac = new CoqTactic(pgraphs.get(g).pgraph.vertices.get(w));
                    nTac.id = id;

                    // if the input arg was not created before, it is a fresh arg
                    for (CoqTactic.Prop inArg : nTac.inputs) {
                        if (inArg.type.equals(CoqTactic.PROP_TYPE.HYP) && !argReplace.containsKey(inArg.name)) {
                            argReplace.put(inArg.name, CoqTactic.Prop.popHypName(argReplace.size()));
                        }
                    }

                    for (CoqTactic.Prop outArg : nTac.outputs) {
                        if (outArg.type.equals(CoqTactic.PROP_TYPE.HYP) && !argReplace.containsKey(outArg.name)) {
                            argReplace.put(outArg.name, CoqTactic.Prop.popHypName(argReplace.size()));
                        }
                    }
                    tactics.add(nTac);
                    id++;
                    break;
                }
            }
        }

        // update args
        for (CoqTactic t: tactics) {
            System.out.println(t.toCoqScript());
            List<CoqTactic.Prop> ins = t.inputs;
//            System.out.println("input raw: " + t.inputs);
            t.inputs = new ArrayList<>();
            for (int h = 0; h < ins.size(); h++) {
                CoqTactic.Prop inArg = ins.get(h);
                if (inArg.type.equals(CoqTactic.PROP_TYPE.HYP)) {
                    t.inputs.add(new CoqTactic.Prop(argReplace.get(inArg.name)));
                } else {
                    t.inputs.add(new CoqTactic.Prop(inArg.name));
                }
            }
//            System.out.println("input: " + t.inputs);

            List<CoqTactic.Prop> outs = t.outputs;
//            System.out.println("output raw: " + t.outputs);
            t.outputs = new ArrayList<>();
            for (int h = 0; h < outs.size(); h++) {
                CoqTactic.Prop outArg = outs.get(h);
                if (outArg.type.equals(CoqTactic.PROP_TYPE.HYP)) {
                    t.outputs.add(new CoqTactic.Prop(argReplace.get(outArg.name)));
                } else {
                    t.outputs.add(new CoqTactic.Prop(outArg.name));
                }
            }
//            System.out.println("output: " + t.outputs);
        }

        String ltacName = "custom";
        String tacScript = tacticsToLtacScript(tactics, ltacName).get(1);

        return new CoqProof(ltacName, tactics, tacScript, CoqProof.SequenceType.LTAC);
    }

    private List<Integer> sortedVertices(List<Integer> vertices) {
        // for each source, construct the list of tactics

        // digraph is a map:
        //   key: a node
        // value: an array of adjacent neighboring nodes

        // construct a hash mapping nodes to their indegrees
        Map<Integer, Integer> indegrees = new HashMap<>();
        Map<Integer, Set<Integer>> neighbors = new HashMap<>();
        for (int v : vertices) {
            indegrees.put(v, 0);
            for (int w : vertices) {
                for (int m = 0; m < this.metadataList.size(); m++) {
                    int add = m * this.vCFCount;
                    if (this.mcsSol.contains(this.CFVars[0][w - 1][v - 1] + add)) {
                        indegrees.put(v, indegrees.get(v) + 1);
                        break;
                    }
                }
            }
//            System.out.println("vertex " + v + " has " + indegrees.get(v) + " incoming edges");
            neighbors.put(v, new HashSet<>());
            for (int w : vertices) {
                for (int m = 0; m < this.metadataList.size(); m++) {
                    int add = m * this.vCFCount;
                    if (this.mcsSol.contains(this.CFVars[0][v - 1][w - 1] + add)) {
                        neighbors.get(v).add(w);
                        break;
                    }
                }
            }
        }

        // track nodes with no incoming edges
        Queue<Integer> sources = new ArrayDeque<>();
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
            int v = sources.poll();
//            System.out.println(v + " is the next source");
            topologicalOrdering.add(v);

            // decremenet the indegree of that node's neighbors
            for (int w: neighbors.get(v)) {
                indegrees.put(w, indegrees.get(w) - 1);
                if (indegrees.get(w) == 0) {
                    sources.add(w);
                }
            }
        }

        // we've run out of nodes with no incoming edges
        // did we add all the nodes or find a cycle?
        if (topologicalOrdering.size() != vertices.size()) {
            throw new IllegalArgumentException("Graph has a cycle! No topological ordering exists.");
        }

        return topologicalOrdering;
    }



    // given a list of integers representing the maxSAT solution,
    // output the corresponding ProofGraph
    public ProofGraph maxSATSolToGraph(List<Integer> solution, boolean printStat) {
        this.updatedSol = solution;

        List<Integer> vertices = solution.stream().filter(p -> p <= this.vCount)
                                        .map(v -> v - 1).collect(Collectors.toList());
        List<CoqTactic> tactics = new ArrayList<>();

        // check where these vertices are mapped to, and
        // copy the in and out subnode lists from there
        Map<Integer, Integer> mapToG1 = new HashMap<>();
        for (int v : vertices) {
            for (int w = 0; w < gVertexSize(1); w++) {
                if (solution.contains(domainVars[v][1][w])) {
                    if (mapToG1.containsKey(v))
                        System.out.println("shit this is bad, for now"); // LOL
                    mapToG1.put(v, w);
                }
            }
        }

        // if (printStat) {
        //    printMappingInfo(solution);
        //    printEdgeInfo(solution);
        // }

        int id = 0;
        List<CoqTactic> pgv = this.pgraphs.get(1).pgraph.vertices;
        for (int w: mapToG1.values().stream().sorted().collect(Collectors.toList())) {
            CoqTactic nTac = new CoqTactic(pgv.get(w));
            nTac.id = id;
            tactics.add(nTac);
            id++;
        }

        ProofGraph pg = new ProofGraph(tactics);
        return pg;
    }

    /*
      @ mcsVertices: mcs vertex ids, starting from 1
      @ g: graph id
     */
    public List<Integer> getMappedVerticesFromInputGraph(List<Integer> mcsVertices, int g) {
        List<Integer> res = new ArrayList<>();
        for (int v : mcsVertices) {
            for (int w = 0; w < gVertexSize(g); w++) {
                if (this.mcsSol.contains(domainVars[v-1][g][w])) {
                    res.add(w);
                    break;
                }
            }

        }
        return res;
    }



    // -------------------
    // Helper Methods
    // -------------------

    public Map<String, Integer> countOnePGVertex(ProofGraph pg) {
        Map<String, Integer> vTypeMap = new HashMap<>();
        for (String sig: this.vTypeMap.keySet()) {
            vTypeMap.put(sig, 0);
        }

        for (CoqTactic tactic : pg.vertices) {
            vTypeMap.put(tactic.sig_no_out_arg, vTypeMap.get(tactic.sig_no_out_arg) + 1);
        }

        int count = vTypeMap.values().stream().filter(c -> c > 0).collect(Collectors.toList()).size();
        this.tacSigCount = Math.max(count, this.tacSigCount);
        this.minNumNodes = Math.min(pg.vertices.size(), this.minNumNodes);
        this.maxNumNodes = Math.max(pg.vertices.size(), this.maxNumNodes);
        return vTypeMap;
    }

    public int gVertexSize(int g) {
        return this.pgraphs.get(g).pgraph.vertices.size();
    }

    int maxGraphSize() {
        // count maxVSize to define array dimension
        int maxVSize = 0;
        for (CoqProof pg: this.pgraphs)
            maxVSize = Math.max(maxVSize, pg.pgraph.vertices.size());
        return maxVSize;
    }

    // the following are for debugging purposes
    public void printCounts() {
        System.out.println("vCount: " + this.vCount);
        System.out.println("vDomainCount: " + this.vDomainCount);
        System.out.println("vTypeCount: " + this.vTypeCount);
        System.out.println("vCFCount: " + this.vCFCount);
        System.out.println("vCFMetaCount: " + this.vCFMetaCount);
    }

    public void printMappingInfo(List<Integer> solution) {
        for (int v = 0; v < this.vCount; v++) {
            for (int g = 0; g < this.numGraphs; g++) {
                for (int w = 0; w < gVertexSize(g); w++) {
                    if (solution.contains(domainVars[v][g][w]))
                        System.out.println("var " + domainVars[v][g][w] + ": " +
                                (v + 1) + " is mapped to " +
                                (w + 1) + " at " + (g + 1));
                }
            }
        }
    }

    public String printStat() {
        StringBuilder sb = new StringBuilder("");
        sb.append("Stats ------------------------------\n");
        sb.append("num tactics: " + this.tacSigCount + "\n");
        sb.append("num graphs: " + this.numGraphs + "\n");
        sb.append("num candidates: " + this.vCount + "\n");
        sb.append("num min input nodes: " + this.minNumNodes + "\n");
        sb.append("num max input nodes: " + this.maxNumNodes + "\n");
        sb.append("End Stats ------------------------------\n");

        System.out.println(sb.toString());
        return sb.toString();
    }

    public void printEdgeInfo(List<Integer> solution) {
        for (int m = 0; m < this.metadataList.size(); m++) {
            int add = m * this.vCFCount;
            for (int v = 0; v < this.vCount; v++) {
                for (int w = 0; w < this.vCount; w++) {
                    if (solution.contains(CFVars[0][v][w] + add))
                        System.out.println("var " + (CFVars[0][v][w] + add) +
                                ": at MCS, (" + (v + 1) + ", "
                                + (w + 1) + ") - " + metadataList.get(m).toString());
                }
            }

            for (int g = 0; g < this.numGraphs; g++) {
                for (int v = 0; v < gVertexSize(g); v++) {
                    for (int w = 0; w < gVertexSize(g); w++) {
                        if (solution.contains(CFVars[g + 1][v][w] + add))
                            System.out.println("var " + (CFVars[g + 1][v][w] + add) +
                                    ": at " + (g + 1) + ", (" + (v + 1) + ", "
                            + (w + 1) + ") - " + metadataList.get(m).toString());
                    }
                }
            }

        }
    }

    public List<Integer> getFreeVarAssgned(String file) {
        List<Integer> maxSATSol = MaxSATUtil.getSolutionList(file);

        if (maxSATSol == null) return new ArrayList<>();
        if (maxSATSol.stream().filter(s -> s > 0 && s <= this.vCount).collect(Collectors.toList()).isEmpty()) return new ArrayList<>();

        List<Integer> freeVars = new ArrayList<>();
        for (int i = 0 ; i < this.vCount; i++) {
            freeVars.add(maxSATSol.get(i));
        }

        return freeVars;


    }
}
