package main.enumeration;

import main.encode.CoqProof;
import main.encode.CoqTactic;
import main.proofgraph.ProofGraph;

import java.util.*;
import java.util.stream.Collectors;

import static main.decode.utils.tacticsToLtacScript;

public class Abstraction {
    public static class Hole {
        public CoqTactic u;
        public Set<Integer> fromInds;
        public Hole(CoqTactic u, Set<Integer> fromInds) {
            this.u = u == null? u : new CoqTactic(u);
            if (this.u != null) {
                this.u.inputs = new ArrayList<>();
                this.u.outputs = new ArrayList<>();
            }
            this.fromInds = new HashSet<>(fromInds);
        }

        public Hole(Hole h) {
            this.u = new CoqTactic(h.u);
            if (this.u != null) {
                this.u.inputs = new ArrayList<>();
                this.u.outputs = new ArrayList<>();
            }
            this.fromInds = new HashSet<>(h.fromInds);
        }
        @Override
        public boolean equals(Object o) {
            if(! (o instanceof Hole)) return false;

            Hole h = (Hole) o;
            if (this.u == null) return h.u == null && this.fromInds.equals(h.fromInds);
            if (h.u == null) return false;
            return this.u.sig_no_out_arg.equals(h.u.sig_no_out_arg) && this.fromInds.equals(h.fromInds);
        }

        @Override
        public int hashCode(){
            if (this.u == null) return this.fromInds.hashCode();
            return this.u.sig_no_out_arg.hashCode() + this.fromInds.hashCode();
        }
    }

    public static class Instantiation {
        Set<List<Integer>> labels = new HashSet<>();
        String sigU;
        String sigV;
        public Instantiation(String sigU, String sigV, Set<List<Integer>> labels) {
            this.sigU = sigU;
            this.sigV = sigV;
            this.labels = new HashSet<>(labels);
        }

        @Override
        public boolean equals(Object o) {
            if(! (o instanceof Instantiation)) return false;

            Instantiation inst = (Instantiation) o;
            return this.sigV.equals(inst.sigV) &&
                    this.sigU.equals(inst.sigU) &&
                    this.labels.equals(inst.labels);
        }

        @Override
        public int hashCode(){
            return this.sigV.hashCode() + this.sigU.hashCode() + this.labels.hashCode();
        }
    }

    public static class Match {
        public int g;    // input graph identifier
        public Map<CoqTactic, Integer> vertexMap = new HashMap<>();  // abstraction vertex -> input graph vertex index
        public Match(int g, Map<CoqTactic, Integer> vertexMap) {
            this.g = g;
            this.vertexMap = new HashMap<>(vertexMap);
        }

        public Match(Match m) {
            this.g = m.g;
            this.vertexMap = new HashMap<>();
            for (CoqTactic u: m.vertexMap.keySet()) {
                this.vertexMap.put(new CoqTactic(u), m.vertexMap.get(u));
            }
        }

        public String getInfo() {
            StringBuilder sb = new StringBuilder();
            sb.append("g: ").append(g).append("\n");
            for (CoqTactic t: vertexMap.keySet()) {
                sb.append(t.sig_no_out_arg).append(",");
            }
            sb.append("\n");
            return sb.toString();
        }

        @Override
        public boolean equals(Object o) {
            if(! (o instanceof Match)) return false;

            Match m = (Match) o;
            if (this.g != m.g) return false;
            for (CoqTactic t: this.vertexMap.keySet()) {
                if (!m.vertexMap.containsKey(t)) return false;
                if (!m.vertexMap.get(t).equals(this.vertexMap.get(t))) return false;
            }
            return true;
        }

    }
    public List<CoqTactic> vertices = new ArrayList<>();
    List<ProofGraph.Edge> edges = new ArrayList<>();
    public List<Hole> holes = new ArrayList<>();
    public List<Match> matches = new ArrayList<>();
    public Map<Integer, List<Integer>> inputVerticesMap = new HashMap<>();
    public int utility = 0;
    public int utilityTraining = 0;
    public CoqProof customTactic = null;
    public boolean predefined = false;

    public Abstraction() {}
    public Abstraction(Abstraction a) {
        this.vertices = new ArrayList<>();
        for (CoqTactic v: a.vertices) {
            if (v == null) this.vertices.add(v);
            else this.vertices.add(new CoqTactic(v));
        }
        this.edges = new ArrayList<>(a.edges);
        this.holes = new ArrayList<>(a.holes);
        this.matches = new ArrayList<>();
        for (Match m : a.matches) {
            this.matches.add(new Match(m));
        }
        this.utility = a.utility;
    }
    public Abstraction(List<CoqTactic> vertices, List<ProofGraph.Edge> edges, List<Hole> holes, List<Match> matches) {
        this.vertices = vertices;
        this.edges = edges;
        this.holes = holes;
        this.matches = matches;
    }

    public String getInfo() {
        StringBuilder sb = new StringBuilder();
        sb.append("vertices: ")
                .append(this.vertices.stream().map(v -> v == null? "null" : v.toCoqScript()).collect(Collectors.toList()))
                .append("\n")
                .append("edges:")
                .append(this.edges.toString())
                        .append("\n");
        sb.append("utility: ").append(utility);
        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if(! (o instanceof Abstraction)) return false;
        if (this.vertices.size() != ((Abstraction) o).vertices.size()) return false;
        List<String> sigs = ((Abstraction) o).vertices.stream().map(v -> v.sig_no_out_arg).collect(Collectors.toList());
        for (int i = 0; i < this.vertices.size(); i++) {
            if (this.vertices.get(i) == null)
                System.out.println();
            if (this.vertices.get(i) == null) {
                if (sigs.get(i) != null)
                    return false;
            } else if (!this.vertices.get(i).sig_no_out_arg.equals(sigs.get(i))) {
                return false;
            }
        }
        return this.edges.equals(((Abstraction) o).edges);
    }

    @Override
    public int hashCode() {
        return this.vertices.size() + this.vertices.stream().map(v -> v == null ? "null" : v.sig_no_out_arg).toList().hashCode() + this.edges.hashCode();
    }

    public String matchesInfo() {
        StringBuilder sb = new StringBuilder();
        for (Match m: this.matches) {
            sb.append(m.getInfo())
                    .append("\n");
        }
        return sb.toString();
    }

    public CoqProof getCustomTactic(List<ProofGraph> corpus) {
        this.vertices.remove(null);
        Map<String, String> argReplace = new HashMap<>();
        if (this.matches.isEmpty()) return null;
        List<Map<Integer, Integer>> matchesById = new ArrayList<>();
        for (Match m1: this.matches) {
            matchesById.add(new HashMap<>());
        }

        Match m = this.matches.get(0);
        for (CoqTactic v: this.vertices) {
            CoqTactic oldV = new CoqTactic(v);
            if (v == null) continue;
            for (int im = 1; im < this.matches.size(); im++) {
                matchesById.get(im).put(this.vertices.indexOf(v), this.matches.get(im).vertexMap.get(v));
            }
            if (!m.vertexMap.containsKey(v))
                System.out.println();
            CoqTactic mappedV = corpus.get(m.g).vertices.get(m.vertexMap.get(v));

            // if the input arg was not created before, it is a fresh arg
            v.inputs = new ArrayList<>();
            v.outputs = new ArrayList<>();
            for (CoqTactic.Prop inArg : mappedV.inputs) {
                if (inArg.type.equals(CoqTactic.PROP_TYPE.HYP) && !argReplace.containsKey(inArg.name)) {
                    argReplace.put(inArg.name, CoqTactic.Prop.popHypName(argReplace.size()));
                }
                v.inputs.add(new CoqTactic.Prop(inArg));
            }

            for (CoqTactic.Prop outArg : mappedV.outputs) {
                if (outArg.type.equals(CoqTactic.PROP_TYPE.HYP) && !argReplace.containsKey(outArg.name)) {
                    argReplace.put(outArg.name, CoqTactic.Prop.popHypName(argReplace.size()));
                }
                v.outputs.add(new CoqTactic.Prop(outArg));
            }
            for (Match mat: this.matches) {
                if (mat.vertexMap.containsKey(oldV) && !oldV.equals(v)) {
                    mat.vertexMap.put(v, mat.vertexMap.get(oldV));
                    mat.vertexMap.remove(oldV);
                }
            }
        }

        // update args
        int numNewHyps = argReplace.size();
        for (CoqTactic t: this.vertices) {
            CoqTactic oldT = new CoqTactic(t);
            if (t == null) continue;
            List<CoqTactic.Prop> ins = t.inputs;
            Set<String> namesCurrTac = new HashSet<>();
            t.inputs = new ArrayList<>();
            for (int h = 0; h < ins.size(); h++) {
                CoqTactic.Prop inArg = ins.get(h);
                if (inArg.type.equals(CoqTactic.PROP_TYPE.HYP)) {
                    String replaceHyp = argReplace.get(inArg.name);
                    if (namesCurrTac.contains(replaceHyp)) {
                        replaceHyp = CoqTactic.Prop.popHypName(numNewHyps++);
                    }
                    t.inputs.add(new CoqTactic.Prop(replaceHyp));
                    namesCurrTac.add(replaceHyp);
                } else {
                    t.inputs.add(new CoqTactic.Prop(inArg.name));
                }
            }

            List<CoqTactic.Prop> outs = t.outputs;
            t.outputs = new ArrayList<>();
            for (int h = 0; h < outs.size(); h++) {
                CoqTactic.Prop outArg = outs.get(h);
                if (outArg.type.equals(CoqTactic.PROP_TYPE.HYP)) {
                    String replaceHyp = argReplace.get(outArg.name);
                    if (namesCurrTac.contains(replaceHyp)) {
                        replaceHyp = CoqTactic.Prop.popHypName(numNewHyps++);
                    }
                    t.outputs.add(new CoqTactic.Prop(replaceHyp));
                    namesCurrTac.add(replaceHyp);
                } else {
                    t.outputs.add(new CoqTactic.Prop(outArg.name));
                }
            }
            for (Match mat: this.matches) {
                if (mat.vertexMap.containsKey(oldT) && !oldT.equals(t)) {
                    mat.vertexMap.put(t, mat.vertexMap.get(oldT));
                    mat.vertexMap.remove(oldT);
                }
            }
        }

        // we need to make sure the argMap works on other matches too
        for (int i = 1; i < this.matches.size(); i++) {
            Match mo = this.matches.get(i);
            Map<String, String> cusToOriInput = new HashMap<>();
            for (int v = 0; v < this.vertices.size(); v++) {
                CoqTactic cusV = this.vertices.get(v);
                int a = 0;
                String sig = new String(cusV.sig_no_out_arg);
                while (sig.contains(" _i")) {
                    if (a >= cusV.inputs.size()) {
                        a--;
                    }
                    CoqTactic.Prop in = cusV.inputs.get(a);
                    if (in.type.equals(CoqTactic.PROP_TYPE.GOAL)) {
                        a++;
                        continue;
                    }
                    sig = sig.replaceFirst(" _i", "***");
                    String proofArg;
                    if (corpus.get(mo.g).vertices.get(matchesById.get(i).get(v)).inputs.size() <= a) {
                       proofArg = corpus.get(mo.g).vertices.get(matchesById.get(i).get(v)).inputs.get(a - 1).simpleName();
                    } else {
                       proofArg = corpus.get(mo.g).vertices.get(matchesById.get(i).get(v)).inputs.get(a).simpleName();
                    }
                    if (!cusToOriInput.containsKey(in.name)) cusToOriInput.put(in.name, proofArg);
                    else if (!cusToOriInput.get(in.name).equals(proofArg)) {
                        // we need to replace the current argument with a new arg
                        this.vertices.get(v).inputs.set(a, new CoqTactic.Prop(CoqTactic.Prop.popHypName(numNewHyps++)));
                        cusToOriInput.put(this.vertices.get(v).inputs.get(a).name, proofArg);
                    }
                    a++;
                }
            }

        }

        String ltacName = "custom";
        List<String> genericScriptPair = tacticsToLtacScript(this.vertices, ltacName);
        String tacScript = genericScriptPair.get(1);

        CoqProof t = new CoqProof(genericScriptPair.get(0), this.vertices, tacScript, CoqProof.SequenceType.LTAC);

        List<Match> newMatches = new ArrayList<>();
        for (Match mat: this.matches) {
            Map<CoqTactic, Integer> map = new HashMap<>();
            for (Map.Entry<CoqTactic, Integer> ent: mat.vertexMap.entrySet()) {
                map.put(ent.getKey(), ent.getValue());
            }
            newMatches.add(new Match(mat.g, map));
        }
        this.matches = newMatches;
        t.matches = new HashMap<>(this.inputVerticesMap);
        return t;
    }
}
