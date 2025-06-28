package main.enumeration;

import main.encode.CoqProof;
import main.encode.CoqTactic;
import main.proofgraph.ProofGraph;
import main.enumeration.Abstraction.*;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class GraphEnumerator {
    protected List<ProofGraph> corpus = new ArrayList<>();
    protected List<Integer> trainingIndices = new ArrayList<>();
    Map<String, List<Hole>> holeMap = new HashMap<>();
    protected Map<Abstraction.Hole, List<Instantiation>> instMap = new HashMap<>();
    List<boolean[][]> reachable = new ArrayList<>();
    List<int[][]> numPaths = new ArrayList<>();
    protected Map<Set<Integer>, Abstraction> predefinedAbs = new HashMap<>();
    Map<Set<Integer>, Integer> predThreshold = new HashMap<>();
    public static String topic;
    // if g0 and g1 are long and extremely similar, we calculate the maximum partialUtil that include embeddings into g1 and g2: <g1, <g2, partialUtil>>

    public GraphEnumerator(List<ProofGraph> corpus, List<Integer> trainingIndices) {
        // only learn from training data
        this.corpus = corpus;
        this.trainingIndices = trainingIndices;
        this.holeMap = generateHolesForAll();
        this.instMap = allPossibleInstantiations();

        for (int g = 0; g < this.corpus.size(); g++) {
            int numV = this.corpus.get(g).vertices.size();
            boolean[][] reach = new boolean[numV][numV];
            int[][] path = new int[numV][numV];
            floydWarshall(reach, path, this.corpus.get(g));
            this.reachable.add(reach);
            this.numPaths.add(path);
        }

        if (this.trainingIndices.size() == this.corpus.size()) {
            for (int g1 = 0; g1 < this.corpus.size(); g1++) {
                for (int g2 = g1 + 1; g2 < this.corpus.size(); g2++) {
                    // if #vertices exceeds threshold
                    int threshold = topic.contains("RegAlloc") ? 15 : 60;
                    ProofGraph pg1 = this.corpus.get(g1);
                    ProofGraph pg2 = this.corpus.get(g2);
                    if (pg1.vertices.size() < threshold || pg2.vertices.size() < threshold) continue;
                    if (pg1.vertices.size() <= 100 && pg2.vertices.size() <= 100 && pg1.vertices.size() != pg2.vertices.size()) continue;

                    Map<String, Integer> tacCount1 = pg1.getSigCount();
                    Map<String, Integer> tacCount2 = pg2.getSigCount();

                    // if the two tacCount are 90% close to each other
                    if (tacCount1.size() != tacCount2.size()) continue;

                    int numSameTacCounts = 0;
                    for (String sig: tacCount1.keySet()) {
                        if (tacCount2.containsKey(sig) && tacCount1.get(sig) == tacCount2.get(sig)) {
                            numSameTacCounts++;
                        }
                    }

                    double percentSimilar = (double) numSameTacCounts / tacCount1.size();
                    if (percentSimilar <= 0.55) continue;

                    // if gets here, we need to explore the graph and count similarity
                    Abstraction abs = maxOverlap(g1, g2);
                    this.predThreshold.put(new HashSet<>(Arrays.asList(g1, g2)), abs.vertices.size());
                    this.predefinedAbs.put(new HashSet<>(Arrays.asList(g1, g2)), abs);
                }
            }
        }
    }

    public Abstraction maxOverlapDiffSize(int gB, int gS) {
        ProofGraph pgB = this.corpus.get(gB);
        ProofGraph pgS = this.corpus.get(gS);
        SortedMap<Integer, Integer> bToS = new TreeMap<>();

        for (int vb = 2; vb < pgB.vertices.size(); vb++) {
            if (pgB.adjList.get(vb).isEmpty()) continue;
            if (bToS.isEmpty()) {
                // find the root
                int vs = 0;
                if (vs >= pgS.vertices.size() || vb >= pgB.vertices.size())
                    System.out.println();
                while (!pgS.vertices.get(vs).sig_no_out_arg.equals(pgB.vertices.get(vb).sig_no_out_arg)) vs++;
                // gets here, we've found the root
                bToS.put(vb, vs);
            }

            // the map should have the corresponding vs for current vs at this point if there exists a match
            if (!bToS.containsKey(vb)) continue;
            int vs = bToS.get(vb);
            List<ProofGraph.Edge> edgesS = pgS.adjList.get(vs);
            int esInd = 0;
            // note: the assumption here is that the big graph always has more edges per vertex, but if it is not true, it just
            //       slightly affects the performance, but no effect on correctness
            int sizeIncrease = 0;
            while (sizeIncrease == 0) {
                if (esInd >= edgesS.size()) break;
                for (ProofGraph.Edge eb: pgB.adjList.get(vb)) {
                    // if the edges has the u, fromPos, toPos equal, and the signature of v equal, map the v
                    if (esInd == edgesS.size()) break;
                    ProofGraph.Edge es = edgesS.get(esInd);
                    if (eb.fromPos != es.fromPos || eb.toPos != es.toPos) continue;

                    // if from and to equal, check signature of es.v
                    if (!pgB.vertices.get(eb.v).sig_no_out_arg.equals(pgS.vertices.get(es.v).sig_no_out_arg)) continue;

                    // if gets here, we find a map
                    esInd++;
                    if (bToS.containsKey(eb.v)) continue;
                    bToS.put(eb.v, es.v);
                    sizeIncrease++;
                }
                esInd++;
            }
        }

        // the vertices that are not included in the current map should not create corresponding holes (because they cannot be expanded anyways)
        Set<Integer> noHoleVerticesB = new HashSet<>();
        for (int vb = 2; vb < pgB.vertices.size(); vb++) {
            if (!bToS.containsKey(vb)) noHoleVerticesB.add(vb);
        }


        // gets all the vertex reachable by the vertices not included in the map
        Set<Integer> removeB = new HashSet<>();
        for (int vb = 2; vb < pgB.vertices.size(); vb++) {
            if (!bToS.containsKey(vb)) {
                getReachableVertices(pgB, vb, removeB);
            }
        }
        removeB = removeB.stream().filter(b -> bToS.containsKey(b)).collect(Collectors.toSet());
        Set<Integer> removeS = new HashSet<>();
        for (int vs = 2; vs < pgS.vertices.size(); vs++) {
            if (!bToS.values().contains(vs)) {
                getReachableVertices(pgS, vs, removeS);
            }
        }
        removeS = removeS.stream().filter(s -> bToS.values().contains(s)).collect(Collectors.toSet());

        // basically remove all the vertices from the bigger one
        if (removeB.size() >= removeS.size()) {
            for (int b: removeB) bToS.remove(b);
        }

        // construct the abstraction
        Abstraction a = new Abstraction();
        a.vertices = new ArrayList<>();
        a.vertices.add(null);

        a.matches = new ArrayList<>();
        Match mB = new Match(gB, new HashMap<>());
        Match mS = new Match(gS, new HashMap<>());

        Map<Integer, Integer> bToA = new HashMap<>();
        int va = 1;
        for (int vb: bToS.keySet()) {
            CoqTactic c = new CoqTactic(pgB.vertices.get(vb));
            c.inputs = new ArrayList<>();
            c.outputs = new ArrayList<>();
            c.args = new ArrayList<>();
            a.vertices.add(c);

            mB.vertexMap.put(c, vb);
            mS.vertexMap.put(c, bToS.get(vb));
            bToA.put(vb, va++);
        }
        a.matches.add(mB);
        a.matches.add(mS);

        a.edges = new ArrayList<>();
        a.holes = new ArrayList<>();
        for (int vb = 0; vb < pgB.vertices.size(); vb++) {
            // if v is in not in map
            if (!bToS.containsKey(vb)) continue;

            Map<Integer, Set<Integer>> holeFromPos = new HashMap<>();
            // if v is not in remove, find the mapped vertex
            for (ProofGraph.Edge eG: pgB.adjList.get(vb)) {
                // if eG.v is to be removed, we dont want the current edge
                if (!bToS.containsKey(eG.v)) {
                    if (noHoleVerticesB.contains(eG.v)) continue;

                    // if the vertex in noHole create an escape, also don't add current hole
                    // if there exists a vertex w in nohole such that reach(vb, w) and reach(w, eG.v), ignore
                    boolean noHole = false;
                    for (int w: noHoleVerticesB) {
                        if (this.reachable.get(gB)[vb][w] && this.reachable.get(gB)[w][eG.v]) {
                            noHole = true;
                            break;
                        }
                    }
                    if (noHole) continue;

                    if (!holeFromPos.containsKey(eG.v)) holeFromPos.put(eG.v, new HashSet<>());
                    holeFromPos.get(eG.v).add(eG.fromPos);
                    continue;
                }

                // map each edge to abstraction and add it to the list
                ProofGraph.Edge eA = new ProofGraph.Edge(bToA.get(eG.u), bToA.get(eG.v), eG.fromPos, eG.toPos);
                a.edges.add(eA);
            }

            for (Set<Integer> labels: holeFromPos.values()) {
                a.holes.add(new Hole(a.vertices.get(bToA.get(vb)), labels));
            }
        }

        a.utility = 0;
        return a;
    }

    public Abstraction maxOverlap(int g1, int g2) {
        ProofGraph pg1 = this.corpus.get(g1);
        ProofGraph pg2 = this.corpus.get(g2);
        Set<Integer> remove1 = new HashSet<>();
        Set<Integer> remove2 = new HashSet<>();

        if (pg1.vertices.size() != pg2.vertices.size()) {
            int small = pg1.vertices.size() < pg2.vertices.size() ? g1 : g2;
            int big = small == g1 ? g2 : g1;
            return maxOverlapDiffSize(big, small);
        }

        // starting from the first vertex, do dfs
        for (int i = 0; i < pg1.vertices.size(); i++) {
            Map<Integer, Set<List<Integer>>> childLabel1 = new HashMap<>();
            Map<Integer, Set<List<Integer>>> childLabel2 = new HashMap<>();
            List<ProofGraph.Edge> edges1 = pg1.adjList.get(i);
            List<ProofGraph.Edge> edges2 = pg2.adjList.get(i);

            for (int j = 0; j < edges1.size(); j++) {
                ProofGraph.Edge e = edges1.get(j);
                if (!childLabel1.containsKey(e.v)) childLabel1.put(e.v, new HashSet<>());
                childLabel1.get(e.v).add(Arrays.asList(e.fromPos, e.toPos));
            }

            for (int j = 0; j < edges2.size(); j++) {
                ProofGraph.Edge e = edges2.get(j);
                if (!childLabel2.containsKey(e.v)) childLabel2.put(e.v, new HashSet<>());
                childLabel2.get(e.v).add(Arrays.asList(e.fromPos, e.toPos));
            }

            for (int child1: childLabel1.keySet()) {
                if (!childLabel2.containsKey(child1) ||
                        !childLabel2.get(child1).equals(childLabel1.get(child1)) ||
                        !pg1.vertices.get(child1).sig_no_out_arg.equals(pg2.vertices.get(child1).sig_no_out_arg)) {
                    remove1.add(child1);
                }
            }

            for (int child2: childLabel2.keySet()) {
                if (!childLabel1.containsKey(child2) ||
                        !childLabel1.get(child2).equals(childLabel2.get(child2)) ||
                        !pg1.vertices.get(child2).sig_no_out_arg.equals(pg2.vertices.get(child2).sig_no_out_arg)) {
                    remove2.add(child2);
                }
            }
        }

        Set<Integer> reach1 = new HashSet<>();
        Set<Integer> reach2 = new HashSet<>();

        for (int r1: remove1) getReachableVertices(pg1, r1, reach1);
        for (int r2: remove2) getReachableVertices(pg2, r2, reach2);

        SortedMap<Integer, Integer> g1ToA = new TreeMap<>();
        SortedMap<Integer, Integer> g2ToA = new TreeMap<>();

        int numRemoved1 = 0;
        int numRemoved2 = 0;
        for (int v = 0; v < pg1.vertices.size(); v++) {
            if (reach1.contains(v)) {
                numRemoved1++;
            } else {
                // if remove does not contain curr vertex
                g1ToA.put(v, v - numRemoved1);
            }
            if (reach2.contains(v)) {
                numRemoved2++;
            } else {
                // if remove does not contain curr vertex
                g2ToA.put(v, v - numRemoved2);
            }
        }

        Abstraction a = new Abstraction();
        a.vertices = new ArrayList<>();
        for (int v: g1ToA.keySet()) {
            if (a.vertices.isEmpty()) {
                a.vertices.add(null);
                continue;
            }
            CoqTactic c = new CoqTactic(pg1.vertices.get(v));
            c.inputs = new ArrayList<>();
            c.outputs = new ArrayList<>();
            c.args = new ArrayList<>();
            a.vertices.add(c);
        }

        a.edges = new ArrayList<>();
        a.holes = new ArrayList<>();
        for (int v = 0; v < pg1.vertices.size(); v++) {
            // if v is in remove, ignore it
            if (reach1.contains(v)) continue;

            Map<Integer, Set<Integer>> holeFromPos = new HashMap<>();
            // if v is not in remove, find the mapped vertex
            for (ProofGraph.Edge eG: pg1.adjList.get(v)) {
                // if eG.v is to be removed, we dont want the current edge
                if (reach1.contains(eG.v)) {
                    if (!holeFromPos.containsKey(eG.v)) holeFromPos.put(eG.v, new HashSet<>());
                    holeFromPos.get(eG.v).add(eG.fromPos);
                    continue;
                }

                // map each edge to abstraction and add it to the list
                ProofGraph.Edge eA = new ProofGraph.Edge(g1ToA.get(eG.u), g1ToA.get(eG.v), eG.fromPos, eG.toPos);
                a.edges.add(eA);
            }

            for (Set<Integer> labels: holeFromPos.values().stream().distinct().collect(Collectors.toSet())) {
                a.holes.add(new Hole(a.vertices.get(g1ToA.get(v)), labels));
            }
        }

        a.matches = new ArrayList<>();
        Match m1 = new Match(g1, new HashMap<>());
        for (int vG: g1ToA.keySet()) {
            if (vG == 0) continue;
            m1.vertexMap.put(a.vertices.get(g1ToA.get(vG)), vG);
        }
        Match m2 = new Match(g2, new HashMap<>());
        for (int vG: g2ToA.keySet()) {
            if (vG == 0) continue;
            if (g2ToA.get(vG) >= a.vertices.size())
                System.out.println();
            m2.vertexMap.put(a.vertices.get(g2ToA.get(vG)), vG);
        }
        a.matches.add(m1);
        a.matches.add(m2);

        a.utility = 0;

        a.predefined = true;
        return a;
    }

    private void getReachableVertices(ProofGraph pg, int v, Set<Integer> reach) {
        // add the vertex if of all the vertices reachable from v
        if (reach.contains(v)) return;
        reach.add(v);
        for (ProofGraph.Edge e: pg.adjList.get(v)) {
            if (!reach.contains(e.v)) {
                getReachableVertices(pg, e.v, reach);
            }
        }
    }


    // returns map where key = sig_with_no_out_args, values = list of holes

    // further pruning: only learn the holes if the hole appear more than once
    public Map<String, List<Hole>> generateHolesForAll() {
        // Map each hope to its count
        Map<Hole, Integer> holeCount = new HashMap<>();
        Map<String, List<Hole>> holeMap = new HashMap<>();
        for (ProofGraph pg: this.corpus.stream().filter(p -> this.trainingIndices.contains(this.corpus.indexOf(p))).toList()) {
            for (int v = 0; v < pg.vertices.size(); v++) {
                String sig = pg.vertices.get(v).sig_no_out_arg;
                if (sig.contains("Lemma ") || sig.contains("Corollary ") || sig.contains("Remark ") ||
                        sig.contains("Theorem ") || sig.contains("Definition ") || sig.contains("Next Obligation")) continue;
                if (!holeMap.containsKey(sig))
                    holeMap.put(sig, new ArrayList<>());
                Map<Integer, Set<Integer>> childLabels = new HashMap<>();
                for (ProofGraph.Edge e : pg.adjList.get(v)) {
                    if (!childLabels.containsKey(e.v)) childLabels.put(e.v, new HashSet<>());
                    childLabels.get(e.v).add(e.fromPos);
                }
                for (Map.Entry<Integer, Set<Integer>> childLabel: childLabels.entrySet()) {
                    Hole newHole = new Hole(pg.vertices.get(v), childLabel.getValue());
                    holeCount.put(newHole, holeCount.getOrDefault(newHole, 0) + 1);
                    if (!holeMap.get(sig).contains(newHole))
                        holeMap.get(sig).add(newHole);
                }
            }
        }
        for (String sig: holeMap.keySet()) {
            // remove hole if only appeared once
            Set<Hole> remove = new HashSet<>();
            for (Hole h: holeMap.get(sig)) {
                if (holeCount.get(h) == 1) {
                    remove.add(h);
                }
            }
            holeMap.get(sig).removeAll(remove);
        }

        return holeMap;
    }
    public Map<Hole, List<Instantiation>> allPossibleInstantiations() {
        Set<String> distinctTacSigs = new HashSet<>();
        // Map each instantiation to a count
        Map<Instantiation, Integer> instCount = new HashMap<>();
        Map<Hole, List<Instantiation>> instMap = new HashMap<>();
        for (ProofGraph pg: this.corpus.stream().filter(p -> this.trainingIndices.contains(this.corpus.indexOf(p))).toList()) {
            for (int u = 0; u < pg.vertices.size(); u++) {
                distinctTacSigs.add(pg.vertices.get(u).sig_no_out_arg);
                List<ProofGraph.Edge> edgesFromU = pg.adjList.get(u);
                Map<Integer, Set<List<Integer>>> childLabels = new HashMap<>();
                for (ProofGraph.Edge e : edgesFromU) {
                    if (!childLabels.containsKey(e.v)) childLabels.put(e.v, new HashSet<>());
                    childLabels.get(e.v).add(Arrays.asList(e.fromPos, e.toPos));
                }
                // child label: key: e.v, value: list of (fromPos, toPos) pairs for the edge(e.u, e.v)
                for (Map.Entry<Integer, Set<List<Integer>>> childLabel: childLabels.entrySet()) {
                    // h: key: e.u, list of toPos for the edges between u and childLabel.getKey (one of e.u's children)
                    Hole h = new Hole(pg.vertices.get(u), childLabel.getValue().stream().map(l -> l.get(0)).collect(Collectors.toSet()));
                    if (!instMap.containsKey(h)) {
                        List<Instantiation> emptyList = new ArrayList<>();
                        emptyList.add(null);
                        instMap.put(h, emptyList);
                    }
                    Instantiation inst = new Instantiation(pg.vertices.get(u).sig_no_out_arg,
                            pg.vertices.get(childLabel.getKey()).sig_no_out_arg, childLabel.getValue());
                    instCount.put(inst, instCount.getOrDefault(inst, 0) + 1);
                    if (!instMap.get(h).contains(inst)) {
                        instMap.get(h).add(inst);
                    }
                }
            }
        }

        distinctTacSigs = distinctTacSigs.stream().filter(s -> !s.contains("Lemma ") && !s.contains("Remark ") &&
                !s.contains("Corollary ") && !s.contains("Theorem ") &&
                !s.contains("Definition ") && !s.contains("Next Obligation")).collect(Collectors.toSet());
        for (Hole h: instMap.keySet()) {
            Set<Instantiation> toRemove = new HashSet<>();
            for (Instantiation inst: instMap.get(h)) {
                if (inst == null) continue;
                if (instCount.get(inst) == 1) {
                    toRemove.add(inst);
                }
            }
            instMap.get(h).removeAll(toRemove);
        }

        // instantiation rule for the starting dummy root A?? := ({∅}, {∅}, {})
        instMap.put(new Hole(null, new HashSet<>(Arrays.asList(-1))),
                distinctTacSigs.stream().map(s -> new Instantiation(null, s, new HashSet<>(Arrays.asList(Arrays.asList(-1, -1))))).collect(Collectors.toList()));
        return instMap;
    }

    // given the set of instantiations, abstraction A??, hole h to instantiate, and holeMap
    // return all the possible instantiations of A?? with h filled
    public List<Abstraction> instantiateAll(Abstraction abst, Hole h, List<Instantiation> instantiations) {
        List<Abstraction> allAbstr = new ArrayList<>();
        if (instantiations == null) {
            Abstraction newA = new Abstraction(abst);
            newA.holes.remove(h);
            allAbstr.add(newA);
            return allAbstr;
        }
        for (Instantiation inst: instantiations) {
            allAbstr.addAll(instantiate(abst, h, inst));
        }
        return allAbstr;
    }

    public List<Abstraction> instantiate(Abstraction a, Hole h, Instantiation inst) {
        if (inst == null) {
            Abstraction newA = new Abstraction(a);
            newA.holes.remove(h);
            // if e suggest terminating instantiation rule
            if (newA.matches.size() > 1)
                return Arrays.asList(newA);
            else
                return new ArrayList<>();
        }

        String instVertexSig = inst.sigV;
	    // if there exists a vertex u' == u in V(A??), where u' -!-> v,
	    // the hole can be filled with (v, u', (i, j))
        List<Abstraction> newAbstractions = new ArrayList<>();
        //for u' in A??.vertices:
        for (CoqTactic v: a.vertices) {
            if (v == null || v.id == h.u.id) continue;
            // if u' != u or u' reaches v in A??
            if (!v.sig_no_out_arg.equals(instVertexSig) || reaches(a, v.id, h.u.id))
                continue;

            Abstraction newA = new Abstraction(a);
            newA.holes.remove(h);
            for (List<Integer> label: inst.labels) {
                newA.edges.add(new ProofGraph.Edge(h.u.id, v.id, label.get(0), label.get(1)));
            }

            // update matches:
            // A??.matches is a list of tuples [(g, f)..], where g is matched input graph,
            // and f is the corresponding vertex mapping f: V(A??) -> V(g)
            List<Match> matchCopies = new ArrayList<>(newA.matches);
            for (Match m: matchCopies) {
                int gUID = getMappedVertexID(h, m);
                List<ProofGraph.Edge> edgesU = this.corpus.get(m.g).adjList.get(gUID);
                Set<List<Integer>> labelsUV = new HashSet<>();
                for (ProofGraph.Edge e: edgesU) {
                    if (!this.corpus.get(m.g).vertices.get(e.v).sig_no_out_arg.equals(v.sig_no_out_arg)) continue;
                    labelsUV.add(Arrays.asList(e.fromPos, e.toPos));
                }
                if (!labelsUV.equals(inst.labels)) {
                    newA.matches.remove(m);
                }
            }
            // useful only if matches is not empty
            if (newA.matches.stream().filter(m -> this.trainingIndices.contains(m.g)).toList().size() > 1) {
                if (ifPartialAbsCollapsible(newA))
                    newAbstractions.add(newA);
            }
        }

        // add new vertex u
        Abstraction newA = new Abstraction(a);
        newA.holes.remove(h);
        CoqTactic addedTac = new CoqTactic(newA.vertices.size(), inst.sigV, inst.sigV, new ArrayList<>(), new ArrayList<>());
        newA.vertices.add(addedTac);

        for (Hole newH: this.holeMap.get(inst.sigV)) {
            Hole hCopy = new Hole(newH);
            hCopy.u.id = addedTac.id;

            // when adding a hole, if newA only has two matches, and the child of the holes do not match, then we do not add the hole
            if (this.corpus.size() == this.trainingIndices.size() && a.matches.size() == 2) {
                // get n-th child of the two matches
                Match m0 = a.matches.get(0);
                Match m1 = a.matches.get(1);

                Set<Integer> key = new HashSet<>(Arrays.asList(m0.g, m1.g));
                if (predefinedAbs.containsKey(key)) {
                    Abstraction absTemp = predefinedAbs.get(key);
                    if (absTemp.holes.stream().map(hl -> hl.u).toList().contains(newH.u)) {
                        // if it's a useless hole just do not add it
                        if (!absTemp.holes.contains(newH)) continue;
                    }
                }
                int v0 = getMappedVertexID(h, m0);
                int v1 = getMappedVertexID(h, m1);

                // get i-th outgoing edge of f(v) in g
                int child0 = this.corpus.get(m0.g).getNthChildID(v0, new ArrayList<>(h.fromInds).get(0));
                int child1 = this.corpus.get(m1.g).getNthChildID(v1, new ArrayList<>(h.fromInds).get(0));

                // if other child does not exist, or they don't match for the two matches, we need to remove the hole
                if (child0 == -1 || child1 == -1 ||
                        !this.corpus.get(m0.g).vertices.get(child0).sig_no_out_arg.equals(this.corpus.get(m1.g).vertices.get(child1).sig_no_out_arg))
                    continue;
            }
            newA.holes.add(hCopy);
        }

        // if initial empty abstraction
        if (a.vertices.size() == 1 && a.vertices.get(0) == null) {
            for (int g = 0; g < this.corpus.size(); g++) {
                ProofGraph pg = this.corpus.get(g);
                for (int v = 0; v < pg.vertices.size(); v++) {
                    if (pg.vertices.get(v).sig_no_out_arg.equals(addedTac.sig_no_out_arg)) {
                        Map<CoqTactic, Integer> newMap = new HashMap<>();
                        newMap.put(addedTac, v);
                        newA.matches.add(new Match(g, newMap));
                    }
                }
            }
            if (newA.matches.stream().filter(m -> this.trainingIndices.contains(m.g)).toList().size() > 1)
                newAbstractions.add(newA);
            return newAbstractions;
        }

        for (List<Integer> label: inst.labels) {
            newA.edges.add(new ProofGraph.Edge(h.u.id, addedTac.id, label.get(0), label.get(1)));
        }
        // update matches: retain and update match if
        // there is a corresponding vertex + edge in match.g that matches curr instantiation
        int i = 0;
        Set<Match> removeMatches = new HashSet<>();
        for (Match m: newA.matches) {
            int gUID = getMappedVertexID(h, m);
            List<Integer> gChildVertexID = new ArrayList<>();
            boolean noMatch = false;
            for (List<Integer> labelInst: inst.labels) {
                boolean foundLabel = false;
                for (ProofGraph.Edge e: this.corpus.get(m.g).adjList.get(gUID)) {
                    if (e.fromPos == labelInst.get(0) && e.toPos == labelInst.get(1)) {
                        foundLabel = true;
                        gChildVertexID.add(e.v);
                        break;
                    }
                }
                if (!foundLabel) {
                    noMatch = true;
                    break;
                }
            }

            if (!noMatch) {
                // all vertex id needs to be the same
                int v = gChildVertexID.get(0);
                for (int id: gChildVertexID) {
                    if (v != id || !this.corpus.get(m.g).vertices.get(id).sig_no_out_arg.equals(addedTac.sig_no_out_arg)) {
                        noMatch = true;
                        break;
                    }
                }

                // vertex not already existed
                if (!noMatch) {
                    noMatch = m.vertexMap.values().contains(v);
                }
            }

            if (noMatch) {
                removeMatches.add(newA.matches.get(i));
            } else {
                // update current match
                newA.matches.get(i).vertexMap.put(addedTac, gChildVertexID.get(0));
            }
            i++;
        }
        for (Match m: removeMatches) {
            newA.matches.remove(m);
        }

        if (newA.matches.stream().filter(m -> this.trainingIndices.contains(m.g)).toList().size() > 1) {
            if (ifPartialAbsCollapsible(newA))
                newAbstractions.add(newA);
        }
        return newAbstractions;
    }

    public boolean reaches(Abstraction a, int parentID, int childID) {
        Set<ProofGraph.Edge> edges = new HashSet<>(a.edges.stream().filter(e -> e.u == parentID).collect(Collectors.toList()));
        while (!edges.isEmpty()) {
            Set<ProofGraph.Edge> newEdges = new HashSet<>();
            for (ProofGraph.Edge e: edges) {
                if (e.v == childID) return true;
                newEdges.addAll(a.edges.stream().filter(ed -> ed.u == e.v).collect(Collectors.toList()));
            }
            edges = new HashSet<>(newEdges);
        }
        return false;
    }

    public List<Abstraction> enumerateAbstractions(boolean greedyP) {
        // vertex-set, edge-set, holes, matches
        Abstraction abst = new Abstraction();  // starting with dummy vertex
        List<Abstraction> res = new ArrayList<>();
        abst.vertices.add(null);
        abst.holes.add(new Hole(null, new HashSet<>(Arrays.asList(-1))));

        PriorityQueue<Abstraction> pq = new PriorityQueue<>(
                (a1, a2) -> {
                    int verticesComparison = Integer.compare(a2.vertices.size(), a1.vertices.size());
                    if (verticesComparison != 0) {
                        return verticesComparison; // Sort primarily by vertices.size in descending order
                    }
                    return Integer.compare(a1.holes.size(), a2.holes.size()); // Sort secondarily by holes.size in descending order
                }
        );
        pq.add(abst);
        if (this.trainingIndices.size() == this.corpus.size()) {
            for (Abstraction a: predefinedAbs.values()) {
                pq.add(a);
            }
        }

        Abstraction bestAbst = null;
        int bestUtil = 0;

        Set<Abstraction> visited = new HashSet<>();
        while (!pq.isEmpty()) {
            abst = pq.poll();                 // Next partial abstraction to instantiate

            if (abst.holes.isEmpty() && !abst.predefined)
                continue;
            Hole h = abst.holes.isEmpty() ? null: abst.holes.get(0);
            // for the chosen hole, instantiate and get new abstractions
            for (Abstraction a: instantiateAll(abst, h, instMap.get(h))) {
                if (!a.holes.isEmpty()) {
                    int partialUtil = partialUtil(a);
                    if (this.corpus.size() == this.trainingIndices.size() && a.matches.size() == 2) {
                        Set<Integer> matchGIDs = a.matches.stream().map(m -> m.g).collect(Collectors.toSet());
                        if (this.predThreshold.containsKey(matchGIDs) && a.vertices.size() < this.predThreshold.get(matchGIDs)) continue;
                    }
                    if (greedyP && partialUtil <= bestUtil) continue;
                    // still partial abstraction
                    if (partialUtil > 0)
                        pq.add(a);
                } else {
                    if (a.vertices.stream().filter(v -> v != null).toList().size() <= 1) continue;
                    if (visited.contains(a)) continue;
                    visited.add(a);
                    a.customTactic = a.getCustomTactic(corpus);
                    List<Integer> completeUtils = completeUtils(a);
                    if (a.matches.size() < 2)
                        continue;
                    int completeUtil = completeUtils.get(0);
                    int completeUtilTraining = completeUtils.get(1);
                    if (completeUtilTraining == completeUtil) {
                        completeUtilTraining = 0;
                    }
                    if (greedyP) {
                        if (completeUtil - completeUtilTraining > bestUtil) {
                            bestAbst = new Abstraction(a);
                            bestUtil = completeUtil - completeUtilTraining;
                            bestAbst.inputVerticesMap = a.inputVerticesMap;
                            bestAbst.utility = completeUtil;
                            bestAbst.utilityTraining = completeUtilTraining;
                            bestAbst.customTactic = a.customTactic;
                            bestAbst.customTactic.matches = new HashMap<>();
                            for (Match m: a.matches) {
                                List<Integer> mappedIDs = a.customTactic.tactics.stream().map(t -> m.vertexMap.get(t)).toList();
                                if (!bestAbst.customTactic.matches.containsKey(m.g)) bestAbst.customTactic.matches.put(m.g, new ArrayList<>());
                                bestAbst.customTactic.matches.get(m.g).addAll(mappedIDs);
                            }
                        }
                    } else {
                        if (completeUtil >= 0 && !res.contains(a)) {
                            Abstraction newA = new Abstraction(a);
                            res.add(newA);
                            newA.inputVerticesMap = a.inputVerticesMap;
                            newA.utility = completeUtil;
                            newA.utilityTraining = completeUtilTraining;
                            newA.customTactic = a.customTactic;
                        }
                    }
                }
            }
        }
        if (greedyP && bestAbst != null) res.add(bestAbst);
        return res;
    }

    public int partialUtil(Abstraction a) {
        // for each match (g, f) of A??, max compression size = maxMatchSize(m) - 1
        // where maxMatchSize(g, f) = A??.vertices.size
        //                            + Sum_{h in A??.holes}(maxHoleSize(h, g)),
        // where maxHoleSize(h = (v, i, u??, ??), g) = reachableVertices(u, g).size,
        // where u is the vertex in g that corresponds to the i-th child of f(v)
        int util = 0;
        int mID = 0;
        Set<Hole> toRemove = new HashSet<>();
        for (Match m: a.matches) {
            if (this.trainingIndices.size() != this.corpus.size() && this.trainingIndices.contains(m.g)) continue;
            util += (a.vertices.size() - 1);
            for (Hole h : a.holes) {
                if (h.u == null) {
                    continue;
                }
                int inputGraphVID = getMappedVertexID(h, m);

                // get i-th outgoing edge of f(v) in g
                int v = this.corpus.get(m.g).getNthChildID(inputGraphVID, new ArrayList<>(h.fromInds).get(0));

                if (v != -1) {
                    // if we have 2 matches currently, and expanding into v means we will lose the other match, we do not add numReachableVertices
                    if (this.corpus.size() == this.trainingIndices.size() && a.matches.size() == 2) {
                        // get n-th child of the other match
                        Match otherMatch = a.matches.get(1 - mID);
                        int otherVID = getMappedVertexID(h, otherMatch);
                        int otherChild = this.corpus.get(otherMatch.g).getNthChildID(otherVID, new ArrayList<>(h.fromInds).get(0));

                        // if other child does not exist, or they don't match for the two matches, we need to remove the hole
                        if (otherChild == -1 || !this.corpus.get(m.g).vertices.get(v).sig_no_out_arg.equals(this.corpus.get(otherMatch.g).vertices.get(otherChild).sig_no_out_arg)) {
                            // remove h
                            toRemove.add(h);
                            continue;
                        }
                    }
                    util += this.corpus.get(m.g).numReachableVertices(v);
                }
            }
            mID++;
        }
        a.holes.removeAll(toRemove);
        return util;
    }

    public boolean ifPartialAbsCollapsible(Abstraction a) {
        Abstraction aCopy = new Abstraction(a);
        CoqProof partialProof = aCopy.getCustomTactic(this.corpus);

        // for matches that appear in the same proof, it is possible they overlap,
        // hence need to find the best set of matches in the proof

        // get the paths and reaches for the partial tactic tdg
        if (partialProof.pgraph == null) partialProof.pgraph = new ProofGraph(partialProof.tactics);
        int numTacV = partialProof.tactics.size();
        boolean[][] reachableTac = new boolean[numTacV][numTacV];
        int[][] numTacPaths = new int[numTacV][numTacV];
        floydWarshall(reachableTac, numTacPaths, partialProof.pgraph);

        // for each match, check if partial abstraction is collapsible by
        int numValidMatches = 0;
        List<Integer> toRemove = new ArrayList<>();
        int i = 0;
        for (Match m: aCopy.matches) {
            // the embedding is only collapsible, if the number of paths equal to each other
            boolean valid = true;
            for (int u = 0; u < numTacV; u++) {
                for (int v = 0; v < numTacV; v++) {
                    int uG = m.vertexMap.get(partialProof.tactics.get(u));
                    int vG = m.vertexMap.get(partialProof.tactics.get(v));
                    if (reachableTac[u][v] && numTacPaths[u][v] != this.numPaths.get(m.g)[uG][vG]) {
                        // if there is no hole from u and (u, v) \in E, then the current tactic is not collapsible
                        if (aCopy.holes.stream().map(h -> h.u).toList().contains(partialProof.tactics.get(u))) continue;
                        if (partialProof.pgraph.adjList.get(u).stream().map(e -> e.v).toList().contains(v)) {
                            valid = false;
                            toRemove.add(i);
                        }
                    }
                    if (!valid) break;
                }
                if (!valid) break;
            }
            i++;
            if (valid) numValidMatches++;
        }

        List<Match> newMatches = new ArrayList<>();
        for (int j = 0; j < a.matches.size(); j++) {
            if (!toRemove.contains(j))
                newMatches.add(a.matches.get(j));
        }
        a.matches = newMatches;

        return numValidMatches > 1;
    }

    public List<Match> filterUnsupportedEvars(List<Match> matches, CoqProof tactic) {
        // pre-check: if tactics do not include any evars, just return matches TODO
        List<Match> res = new ArrayList<>();
        // if m(tac) has > 1 branches, and i-th branch has evar, but i-th branch is not included in m(tac) while j-th, j > i is included, we filter out the current match

        for (Match m : matches) {
            boolean removeMatch = false;
            for (CoqTactic t: tactic.tactics) {
                // if current tactic does not output multiple goals, skip
                List<CoqTactic.Prop> outGoals = t.outputs.stream().filter(o -> o.type.equals(CoqTactic.PROP_TYPE.GOAL)).collect(Collectors.toList());
                if (outGoals == null || outGoals.size() <= 1) continue;

                // if has multiple goals, we need to record the necessary br
                for (int i = 0; i < outGoals.size() - 1; i++) {
                    if (!outGoals.get(i).name.contains("?")) continue;
                    int indV = m.vertexMap.get(t);
                    if (indV == 254)
                        System.out.println();
                    Set<Integer> etacs = getEtacIndexInBranch(m.g, indV, i);

                    // for each goal, if current branch (until resolved) does not include e-tactics, just go to next goal
                    if (etacs.isEmpty()) continue;

                    // if current branch has evars
                    // if the e-tactic in current branch is included, move on to future goals
                    boolean evarsIncluded = true;
                    for (int v: etacs) {
                        if (m.vertexMap.values().contains(v)) continue;
                        evarsIncluded = false;
                        break;
                    }
                    if (evarsIncluded) continue;

                    // if next branch has tactics extracted (if there exists a tactic t, f(t).input_goal in outGoals and c<num> > c<curr-num>)
                    for (CoqTactic t1: tactic.tactics) {
                        if (t1.equals(t)) continue;
                        for (CoqTactic.Prop inputGoal: t1.inputs) {
                            if (outGoals.contains(inputGoal) && outGoals.indexOf(inputGoal) > i) {
                                // remove current match
                                removeMatch = true;
                                break;
                            }
                        }
                        if (removeMatch) break;
                    }
                    if (removeMatch) break;
                }
                if (removeMatch) break;
            }
            if (!removeMatch) res.add(m);
        }

        if (res.size() < matches.size())
            return res;
        return matches;
    }

    // returns the vertex indices in g in current branch that contains evars
    private Set<Integer> getEtacIndexInBranch(int g, int indV, int indGoal) {
        Set<Integer> res = new HashSet<>();

        // find the tactic where the input goal contains ? while the output does not, and return the tactic index
        getEtacsDfs(g, indV, indGoal, res);

        return res;
    }

    private void getEtacsDfs(int g, int indV, int indGoal, Set<Integer> res) {
        // given the parent indV, find all etacs on all branches
        List<CoqTactic> vertices = this.corpus.get(g).vertices;
        if (indGoal >= vertices.get(indV).outputs.stream().filter(o -> o.type.equals(CoqTactic.PROP_TYPE.GOAL)).toList().size())
            return;
        CoqTactic.Prop parentGoal = vertices.get(indV).outputs.stream().filter(o -> o.type.equals(CoqTactic.PROP_TYPE.GOAL)).toList().get(indGoal);

        // find tactic that takes in current goal
        int indU = indV + 1;
        while (indU < vertices.size()) {
            if (vertices.get(indU).inputs.contains(parentGoal)) {
                break;
            }
            indU++;
        }

        // indU takes in the goal - check if it instantiate the goal, if yes, add indU to res, otherwise keep recursing
        List<CoqTactic.Prop> outGoals = vertices.get(indU).outputs.stream().filter(o -> o.type.equals(CoqTactic.PROP_TYPE.GOAL)).toList();
        List<String> inputSymVars = getSymVars(parentGoal.name);

        // if no output goal, then add to result
        if (outGoals.isEmpty()) {
            res.add(indU);
            return;
        }

        for (int gInd = 0; gInd < outGoals.size(); gInd++) {
            List<String> outputSymVars = getSymVars(outGoals.get(gInd).name);
            // if no input sym var is left, add to res and return
            boolean symRemain = false;
            for (String inSym : inputSymVars) {
                if (outputSymVars.contains(inSym)) {
                    symRemain = true;
                } else {
                    res.add(indU);
                }
            }
            if (symRemain) getEtacsDfs(g, indU, gInd, res);
        }
    }

    private List<String> getSymVars(String input) {
        List<String> symVars = new ArrayList<>();
        Pattern pattern = Pattern.compile("\\?\\w+"); // Matches '?' followed by word characters
        Matcher matcher = pattern.matcher(input);

        while (matcher.find()) {
            symVars.add(matcher.group());
        }
        return symVars;
    }

    public List<Match> filterNoncollapsibleMatches(List<Match> matches, CoqProof tactic) {
        List<Match> res = new ArrayList<>();

        // get the paths and reaches for the tactic tdg
        int numTacV = tactic.tactics.size();
        boolean[][] reachableTac = new boolean[numTacV][numTacV];
        int[][] numTacPaths = new int[numTacV][numTacV];
        if (tactic.pgraph == null) tactic.pgraph = new ProofGraph(tactic.tactics);
        floydWarshall(reachableTac, numTacPaths, tactic.pgraph);

        // for each match, filter it out if not collapsible
        for (Match m: matches) {
            boolean add = true;
            // the embedding is only collapsible, if the number of paths equal to each other
            for (int u = 0; u < numTacV; u++) {
                for (int v = 0; v < numTacV; v++) {
                    int uG = m.vertexMap.get(tactic.tactics.get(u));
                    int vG = m.vertexMap.get(tactic.tactics.get(v));
                    if (reachableTac[u][v] && numTacPaths[u][v] != this.numPaths.get(m.g)[uG][vG]) {
                        add = false;
                        break;
                    }
                }
                if (!add) break;
            }
            if (add) res.add(m);
        }

        return res;
    }

    public static void floydWarshall(boolean[][] reach, int[][] path, ProofGraph g) {
        int numV = reach.length;
        for (int i = 0; i < numV; i++) {
            for (int j = 0; j < numV; j++) {
                if (i == j || g.adjList.get(i).stream().map(e -> e.v).toList().contains(j)) {
                    reach[i][j] = true;
                    path[i][j] = 1;
                }
            }
        }

        for (int k = 0; k < numV; k++) {
            for (int i = 0; i < numV; i++) {
                for (int j = 0; j < numV; j++) {
                    if (i == j || j == k || i == k) continue;
                    if (reach[i][k] && reach[k][j]) {
                        reach[i][j] = true;
                        path[i][j] += path[i][k] * path[k][j];
                    }
                }
            }
        }
    }

    public boolean collapsibleMatching(int g, Map<CoqTactic, Integer> map) {
        // if a is a subgraph of b,
        return true;
    }

    // [util, trainingUtil]
    public List<Integer> completeUtils(Abstraction a) {
        a.vertices.remove(null);
        // take account of the abstraction size
        int u = 0;
        int uTraining = u;

        // for matches that appear in the same proof, it is possible they overlap,
        // hence need to find the best set of matches in the proof
        Map<Integer, List<Map<CoqTactic, Integer>>> mMap = new HashMap<>();

        a.matches = filterNoncollapsibleMatches(a.matches, a.customTactic);
        if (a.vertices.size() == 47)
            System.out.println();
        a.matches = filterUnsupportedEvars(a.matches, a.customTactic);

        for (Match m : a.matches) {
            // filter out invalid matching
            if (!mMap.containsKey(m.g)) mMap.put(m.g, new ArrayList<>());
            mMap.get(m.g).add(m.vertexMap);
        }
        int numMatches = 0;
        int numMatchesTraining = 0;
        Map<Integer, List<Integer>> verticesMap = new HashMap<>();
        for (Map.Entry<Integer, List<Map<CoqTactic, Integer>>> entry: mMap.entrySet()) {
            if (!verticesMap.containsKey(entry.getKey())) {
                verticesMap.put(entry.getKey(), new ArrayList<>());
            }
            if (entry.getValue().size() > 1) {
                Set<Set<Integer>> mappedVertices = bestDisjointVertexSet(entry.getKey(), entry.getValue());
                numMatches += mappedVertices.size();
                if (this.trainingIndices.contains(entry.getKey())) {
                    numMatchesTraining += mappedVertices.size();
                }

                // update a.matches
                for (Set<Integer> s: mappedVertices) {
                    for (Integer v: s) {
                        verticesMap.get(entry.getKey()).add(v);
                    }
                }
                if (mappedVertices.size() < entry.getValue().size()) {
                    // remove the removed matches
                    Set<Match> toRemove = new HashSet<>();
                    for (Match m: a.matches) {
                        if (m.g == entry.getKey()) {
                            if (!mappedVertices.contains(new HashSet<>(m.vertexMap.values()))) {
                                // remove current match
                                toRemove.add(m);
                            }
                        }
                    }
                    a.matches.removeAll(toRemove);
                }
            } else {
                for (Integer v: entry.getValue().get(0).values()) {
                    verticesMap.get(entry.getKey()).add(v);
                }
                numMatches += 1;
                if (this.trainingIndices.contains(entry.getKey())) {
                    numMatchesTraining += 1;
                }
            }
        }
        a.inputVerticesMap = verticesMap;

        // for each match location, proof size decrease by (A.size - 1)
        u += (numMatches * (a.vertices.size() - 1));
        uTraining += (numMatchesTraining * (a.vertices.size() - 1));

        return Arrays.asList(u, uTraining);
    }

    public Set<Set<Integer>> bestDisjointVertexSet(int g, List<Map<CoqTactic, Integer>> maps) {
        Set<Set<Set<Integer>>> powerSet = new HashSet<>();
        powerSet.add(new HashSet<>());

        for (Map<CoqTactic, Integer> f : maps) {
            Set<Integer> codomain = new HashSet<>(f.values());  // the vertex set to be added
            Set<Set<Set<Integer>>> pSetCopy = new HashSet<>();
            for (Set<Set<Integer>> vertexSets : powerSet) {
                Set<Set<Integer>> removeSets = new HashSet<>(); // vertex sets to be removed
                for (Set<Integer> vertexSet : vertexSets) {
                    boolean intersect = false;
                    for (int v: vertexSet) {
                        if (codomain.contains(v)) {
                            intersect = true;
                            break;
                        }
                    }
                    if (intersect) {
                        removeSets.add(vertexSet);
                    }
                }
                Set<Set<Integer>> newSet = new HashSet<>(vertexSets);
                if (removeSets.isEmpty()) {
                    newSet.add(codomain);
                } else {
                    newSet.removeAll(removeSets);
                    pSetCopy.add(vertexSets);
                }
                pSetCopy.add(newSet);
            }
            powerSet = new HashSet<>();
            for (Set<Set<Integer>> s: pSetCopy) {
                powerSet.add(s);
            }
        }

        Set<Set<Integer>> bestSets = new HashSet<>();
        for (Set<Set<Integer>> vertexSets : powerSet) {
            if (vertexSets.size() > bestSets.size()) {
                bestSets = vertexSets;
            }
        }
        return bestSets;
    }

    public int getMappedVertexID(Hole h, Match m) {
        CoqTactic abstV = h.u;
        if (m.vertexMap.get(abstV) == null)
            System.out.println();
        return m.vertexMap.get(abstV);
    }
}
