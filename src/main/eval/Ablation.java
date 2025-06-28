package main.eval;

import main.config.BmConfig;
import main.encode.CoqProof;
import main.encode.Encoder;
import main.enumeration.Abstraction;
import main.enumeration.GraphEnumerator;
import main.proofgraph.ProofGraph;

import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

import static main.Main.getLibCandidatesEnumeration;
import static main.config.Path.evalPath;
import static main.config.Path.RQ5;
import static main.decode.utils.writeTo;

public class Ablation {
    public enum AblationType {
        GRAMMAR,
        PRUNING,
        NONE
    }
    AblationType ablationType;
    BmConfig config;
    List<CoqProof> proofs;
    List<Integer> trainingProofs;

    public Ablation(BmConfig config, List<CoqProof> proofs) throws IOException {
        this.ablationType = config.mode == BmConfig.Mode.PRUNING_ABL ? AblationType.PRUNING : (config.mode == BmConfig.Mode.GRAMMAR_ABL ? AblationType.GRAMMAR : AblationType.NONE);
        this.config = config;
        this.proofs = proofs;
        this.trainingProofs = Encoder.getTrainingProofIndices(config, proofs);
    }

    public void runExperiments() throws IOException {
        if (this.ablationType != AblationType.NONE) {
            String ablType = ablationType == AblationType.GRAMMAR ? "grammar" : "pruning";
            System.out.println("running ablation (no " + ablType + ") for " + config.topic);
            Set<CoqProof> candidateTactics = new LinkedHashSet<>();
            List<Long> timePerTac = new ArrayList<>();
            getLibCandidatesEnumeration(proofs, trainingProofs, candidateTactics, true,
                    this.ablationType, timePerTac, this.config.timeout, this.config.topic);

            // File name
            String fileName = evalPath + RQ5 + "no-" + ablType + "-abl/" + config.domain + "/" + config.topic + ".csv";

            // Write to CSV file
            StringBuilder sb = new StringBuilder("numTacs,Time\n");
            // Write the data rows
            for (int i = 0; i < timePerTac.size(); i++) {
                sb.append((i + 1) + "," + timePerTac.get(i) + "\n");
            }
            writeTo(sb.toString(), fileName);
            System.out.println("finished running ablation (no " + ablType + ") for " + config.topic);
        }
    }

    public static class GraphEnumeratorAblationGrammar extends GraphEnumerator {
        Map<String, List<Abstraction.Hole>> holeMap = new HashMap<>();
        Map<Abstraction.Hole, List<Abstraction.Instantiation>> instMap = new HashMap<>();

        // we need to have the threshold, but not the actual abst in here
        Map<Set<Integer>, Integer> predefinedAbs = new HashMap<>();

        public GraphEnumeratorAblationGrammar(List<ProofGraph> corpus, List<Integer> trainingIndices) {
            // only learn from training data
            super(corpus, trainingIndices);
            this.holeMap = generateHolesForAll();
            this.instMap = allPossibleInstantiations();
        }

        @Override
        public Map<Abstraction.Hole, List<Abstraction.Instantiation>> allPossibleInstantiations() {
            // count the max number of input and output for a signature
            Map<String, Integer> maxInput = new HashMap<>();
            Map<String, Integer> maxOutput = new HashMap<>();

            Set<String> distinctTacSigs = new HashSet<>();
            Set<Set<List<Integer>>> distinctPos = new HashSet<>();
            Map<Abstraction.Hole, List<Abstraction.Instantiation>> instMap = new HashMap<>();
            // get all the signatures
            for (ProofGraph pg: corpus.stream().filter(p -> trainingIndices.contains(corpus.indexOf(p))).toList()) {
                for (List<ProofGraph.Edge> edges: pg.adjList) {
                    Map<Integer, Set<List<Integer>>> childLabels = new HashMap<>();
                    for (ProofGraph.Edge e: edges) {
                        String uSig = pg.vertices.get(e.u).sig_no_out_arg;
                        if (uSig.contains("Lemma ") || uSig.contains("Remark ") ||
                                uSig.contains("Corollary ") || uSig.contains("Theorem ") ||
                        uSig.contains("Next Obligation") || uSig.contains("Definition ")) continue;
                        if (!childLabels.containsKey(e.v)) childLabels.put(e.v, new HashSet<>());
                        childLabels.get(e.v).add(Arrays.asList(e.fromPos, e.toPos));

                        String vSig = pg.vertices.get(e.v).sig_no_out_arg;
                            if (!maxOutput.containsKey(uSig) || e.fromPos > maxOutput.get(uSig))
                                maxOutput.put(uSig, e.fromPos);
                            if (!maxInput.containsKey(vSig) || e.toPos > maxInput.get(vSig))
                                maxInput.put(vSig, e.toPos);

                    }
                    if (childLabels.isEmpty()) continue;
                    for (Set<List<Integer>> pos: childLabels.values()) {
                        distinctPos.add(pos);
                    }
                }
            }

            for (ProofGraph pg: corpus.stream().filter(p -> trainingIndices.contains(corpus.indexOf(p))).toList()) {
                for (List<ProofGraph.Edge> es: pg.adjList) {
                    if (es.isEmpty()) continue;
                    int u = es.get(0).u;
                    distinctTacSigs.add(pg.vertices.get(u).sig_no_out_arg);
                    Set<Integer> children = es.stream().map(e -> e.v).collect(Collectors.toSet());
                    for (int v: children) {
                        String sigU = pg.vertices.get(u).sig_no_out_arg;
                        String sigV = pg.vertices.get(v).sig_no_out_arg;
                        if (!maxOutput.containsKey(sigU) || !maxInput.containsKey(sigV)) continue;
                        for (Set<List<Integer>> posPairs: distinctPos) {
                            Set<Integer> fromPoses = posPairs.stream().map(l -> l.get(0)).collect(Collectors.toSet());
                            Set<Integer> toPoses = posPairs.stream().map(l -> l.get(1)).collect(Collectors.toSet());
                            // if the fromPoses or toPoses are out of range, do not expand
                            boolean outRange = false;
                            for (Integer f: fromPoses) {
                                if (f > maxOutput.get(sigU)) {
                                    outRange = true;
                                    break;
                                }
                            }
                            if (outRange) continue;
                            for (Integer t: toPoses) {
                                if (t > maxInput.get(sigV)) {
                                    outRange = true;
                                    break;
                                }
                            }
                            if (outRange) continue;

                            Abstraction.Hole h = new Abstraction.Hole(pg.vertices.get(u), posPairs.stream().map(l -> l.get(0)).collect(Collectors.toSet()));
                            if (!instMap.containsKey(h)) {
                                List<Abstraction.Instantiation> emptyList = new ArrayList<>();
                                emptyList.add(null);
                                instMap.put(h, emptyList);
                            }
                            Abstraction.Instantiation inst = new Abstraction.Instantiation(sigU,
                                    sigV, posPairs);
                            if (!instMap.get(h).contains(inst)) {
                                instMap.get(h).add(inst);
                            }
                        }
                    }
                }
            }

            distinctTacSigs = distinctTacSigs.stream().filter(s -> !s.contains("Lemma ") && !s.contains("Remark ") &&
                    !s.contains("Corollary ") && !s.contains("Theorem ") && !s.contains("Next Obligation") && !s.contains("Definition")).collect(Collectors.toSet());

            // instantiation rule for the starting dummy root A?? := ({∅}, {∅}, {})
            instMap.put(new Abstraction.Hole(null, new HashSet<>(Arrays.asList(-1))),
                    distinctTacSigs.stream().map(s -> new Abstraction.Instantiation(null, s, new HashSet<>(Arrays.asList(Arrays.asList(-1, -1))))).collect(Collectors.toList()));
            return instMap;
        }


        @Override
        public Map<String, List<Abstraction.Hole>> generateHolesForAll() {
            // iterate thru all the edges, get the maximum fromPos and toPost
            Set<String> nonLeaves = new HashSet<>();  // the signatures that are not leaves
            Set<Set<Integer>> fromPos = new HashSet<>();
            Map<String, Integer> maxOutIndex = new HashMap<>();
            for (ProofGraph pg: corpus.stream().filter(p -> trainingIndices.contains(corpus.indexOf(p))).toList()) {
                for (List<ProofGraph.Edge> es: pg.adjList) {
                    Map<Integer, Set<Integer>> childLabels = new HashMap<>();
                    for (ProofGraph.Edge e: es) {
                        String sig = pg.vertices.get(e.u).sig_no_out_arg;
                        if (!maxOutIndex.containsKey(sig)) maxOutIndex.put(sig, -1);
                        if (!childLabels.containsKey(e.v)) childLabels.put(e.v, new HashSet<>());
                        childLabels.get(e.v).add(e.fromPos);
                        if (e.fromPos > maxOutIndex.get(pg.vertices.get(e.u).sig_no_out_arg)) {
                            maxOutIndex.put(sig, e.fromPos);
                        }
                        nonLeaves.add(pg.vertices.get(e.u).sig_no_out_arg);
                    }
                    for (Set<Integer> pos: childLabels.values()) {
                        fromPos.add(pos);
                    }
                }
            }

            Map<String, List<Abstraction.Hole>> holeMap = new HashMap<>();
            for (ProofGraph pg: corpus.stream().filter(p -> trainingIndices.contains(corpus.indexOf(p))).toList()) {
                for (int v = 0; v < pg.vertices.size(); v++) {
                    String sig = pg.vertices.get(v).sig_no_out_arg;
                    if (sig.contains("Lemma ") || sig.contains("Corollary ") || sig.contains("Remark ")
                            || sig.contains("Theorem ") || sig.contains("Next Obligation") || sig.contains("Definition ")) continue;
                    if (!holeMap.containsKey(sig))
                        holeMap.put(sig, new ArrayList<>());
                    if (!nonLeaves.contains(sig)) continue;

                    // add all possible holes to sig.value
                    for (Set<Integer> froms: fromPos) {
                        // get min and max
                        boolean next = false;
                        for (int f: froms) {
                            if (f > maxOutIndex.get(pg.vertices.get(v).sig_no_out_arg)) {
                                next = true;
                                break;
                            }
                        }

                        if (next) continue;
                        Abstraction.Hole newHole = new Abstraction.Hole(pg.vertices.get(v), froms);
                        if (!holeMap.get(sig).contains(newHole))
                            holeMap.get(sig).add(newHole);
                    }
                }
            }
            return holeMap;
        }
    }

    public static class GraphEnumeratorAblationPruning extends GraphEnumerator {
        public GraphEnumeratorAblationPruning(List<ProofGraph> corpus, List<Integer> trainingIndices) {
            // only learn from training data
            super(corpus, trainingIndices);
        }

        @Override
        public List<Abstraction> enumerateAbstractions(boolean greedyP) {
            // vertex-set, edge-set, holes, matches
            Abstraction abst = new Abstraction();  // starting with dummy vertex
            List<Abstraction> res = new ArrayList<>();
            abst.vertices.add(null);
            abst.holes.add(new Abstraction.Hole(null, new HashSet<>(Arrays.asList(-1))));
            PriorityQueue<Abstraction> pq = new PriorityQueue<>((a1, a2) -> this.partialUtil(a2) - this.partialUtil(a1));
            pq.add(abst);
            for (Abstraction predAbs: predefinedAbs.values()) {
                pq.add(predAbs);
            }

            Abstraction bestAbst = null;
            int bestUtil = -1;

            Set<Abstraction> visited = new HashSet<>();
            while (!pq.isEmpty()) {
                abst = pq.poll();                 // Next partial abstraction to instantiate

                if (abst.holes.isEmpty()) continue;
                Abstraction.Hole h = abst.holes.get(0);
                // for the chosen hole, instantiate and get new abstractions
                for (Abstraction a: instantiateAll(abst, h, instMap.get(h))) {
                    if (!a.holes.isEmpty()) {
                        // still partial abstraction
                        if (partialUtil(a) > 0)
                            pq.add(a);
                    } else {
                        if (a.vertices.stream().filter(v -> v != null).toList().size() <= 1) continue;
                        if (visited.contains(a)) continue;
                        visited.add(a);
                        a.customTactic = a.getCustomTactic(corpus);
                        List<Integer> completeUtils = completeUtils(a);
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
                                for (Abstraction.Match m: a.matches) {
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
    }
}
