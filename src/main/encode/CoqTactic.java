package main.encode;

import java.util.*;
import java.util.stream.Collectors;

/*
 A custom representation of Coq tactics, extracted from JSON inputs
 */
public class CoqTactic {

    // Proposition type: can either be a goal or a hypothesis (proposition or definition)
    public enum PROP_TYPE {
        GOAL,
        HYP
    }

    public enum IO_ID {
        IN,
        OUT
    }

    // Proposition defined by the full name string and the type
    public static class Prop {
        public String name;
        public PROP_TYPE type;
        public IO_ID ioId;

        public Prop(String rawName) {
            name = rawName.replace("\n", " ");

            // JSON format for goals is "cxx_goal : <goal>"
            if (rawName.split(" ")[0].contains("_goal")) {
                type = PROP_TYPE.GOAL;
            } else {
                type = PROP_TYPE.HYP;
            }
        }

        public Prop(Prop p) {
            this.type = p.type;
            this.name = new String(p.name);
        }

        public static String popHypName(int hypId) {
            String hypName = "H" + hypId;
            return hypName + " : " + hypName;
        }

        // Return only the name which Coq uses to select propositions
        public String simpleName() {
            if (this.type.equals(PROP_TYPE.HYP)) {
                if (name.split(" : ")[0].contains("_hyp"))
                    return name.substring(name.indexOf(":") + 2).trim();
                String s = name.substring(0, name.indexOf(":") - 1).trim();

                if (s.matches("c\\d+_(\\S+)")) 
                    return s.split("_", 2)[s.split("_", 2).length - 1];
                return s;
            }
            return name.substring(name.indexOf(":") + 2).trim();
        }

        @Override
        public boolean equals(Object o){
            if(! (o instanceof Prop)) return false;

            Prop prop = (Prop) o;
            if (this.type.equals(PROP_TYPE.HYP))
                return this.name.equals(prop.name) && this.type.equals(prop.type);
            String nm = this.name.split(" : ")[0];
            String propNm = prop.name.split(" : ")[0];
            return nm.equals(propNm) && this.type.equals(prop.type);
        }

        @Override
        public int hashCode() {
            if (this.type.equals(PROP_TYPE.HYP))
                return this.name.hashCode(); // Type is encompassed in the name
            return this.name.split(" : ")[0].hashCode();
        }

        @Override
        public String toString() {
            return this.name;
        }
    }

    public int id; // tactic ID in a proof graph
    public String signature; // signature of the tactic, e.g. "apply _ in _"
    public String sig_no_out_arg; // signature of the tactic, e.g. "apply _ in _", without output arguments
    public List<Prop> inputs; // tactic arguments, including goals and hypotheses
    public List<Prop> outputs; // tactic results, including goals and hypotheses
    public List<String> args = new ArrayList<>();
                            // the "arguments" following the tactic signature, for ex,
                            // [H1] is the args for intro H1, [H1 H2 H3] is the args for destruct H1 as H2 H3

    public CoqTactic(String signature, String sig_no_out_arg, List<String> inputs, List<String> outputs) {
        this.signature = signature;
        this.sig_no_out_arg = sig_no_out_arg.contains("intros ") || sig_no_out_arg.contains("intro ") ? signature : sig_no_out_arg;

        this.inputs = new ArrayList<>();
        this.outputs = new ArrayList<>();
        for(int i = 0; i < inputs.size(); i++) {
            this.inputs.add(new Prop(inputs.get(i)));
        }
        for(int i = 0; i < outputs.size(); i++) {
            this.outputs.add(new Prop(outputs.get(i)));
        }
        this.args = serializeArgs(this.gatherArgs(this.sig_no_out_arg)).stream().map(p -> p.simpleName()).toList();
    }


    public CoqTactic(String signature, List<String> inputs, List<String> outputs) {
        this(signature, signature, inputs, outputs);
    }
    public CoqTactic(int id, String signature, String sig_no_out_arg, List<String> inputs, List<String> outputs) {
        this(signature, sig_no_out_arg, inputs, outputs);
        this.id = id;
    }

    public CoqTactic(CoqTactic o) {
        this.id = o.id;
        this.signature = new String(o.signature);
        this.sig_no_out_arg = new String(o.sig_no_out_arg);
        this.inputs = new ArrayList<>();
        this.outputs = new ArrayList<>();
        for(int i = 0; i < o.inputs.size(); i++) {
            this.inputs.add(new Prop(o.inputs.get(i)));
        }
        for(int i = 0; i < o.outputs.size(); i++) {
            this.outputs.add(new Prop(o.outputs.get(i)));
        }
        this.args = new ArrayList<>(o.args);
    }

    public static List<Prop> serializeArgs(Map<String, Prop> argMap) {
        List<Prop> res = new ArrayList<>();
        for (Prop p: argMap.values()) {
            if (p == null) continue;
            res.add(p);
        }
        return res;
    }

    // return key=arg obj, val="in" or "out"
    // return key="in/out"+"<order>", val = prop
    public Map<String, Prop> gatherArgs(String signature) {
        Queue<Prop> inputHyps = new LinkedList<>(this.inputs.stream().filter(in -> in.type.equals(PROP_TYPE.HYP)).collect(Collectors.toList()));
        Queue<Prop> outputHyps = new LinkedList<>(this.outputs.stream().filter(in -> in.type.equals(PROP_TYPE.HYP)).collect(Collectors.toList()));
        Queue<Integer> outArgIndices = new LinkedList<>();
        Queue<Integer> inArgIndices = new LinkedList<>();
        String sig = signature.split(" \\.")[0] + " ";
        while (sig.indexOf(" _o") != -1) {
            outArgIndices.add(sig.indexOf(" _o"));
            sig = sig.replaceFirst(" _o", " ++");
        }

        while (sig.indexOf(" _i") != -1) {
            inArgIndices.add(sig.indexOf(" _i"));
            sig = sig.replaceFirst(" _i", " ++");
        }

        Map<String, Prop> res = new LinkedHashMap<>();
        int order = 0;
        while (!outArgIndices.isEmpty() || !inArgIndices.isEmpty()) {
            boolean addInputArg = false;
            if (outArgIndices.isEmpty() ||
                    (!inArgIndices.isEmpty() && inArgIndices.peek() < outArgIndices.peek())) {
                addInputArg = true;
            }

            // if both indices are not empty, compare them
            if (addInputArg) {
                Prop currP = inputHyps.poll();
                res.put("in" + (order++), currP);
                inArgIndices.poll();
            } else {
                Prop currP = outputHyps.poll();
                res.put("out" + (order++), currP);
                outArgIndices.poll();
            }
        }
        return res;
    }

    public String sigReplaceArgs() {
        String tactic = this.signature.split(" \\.")[0] + " ";

        Map<String, Prop> argMap = this.gatherArgs(this.signature);
        for (String id: argMap.keySet()) {
            String identifier;
            Prop arg = argMap.get(id);
            if (id.contains("in")) {
                identifier = "in";
            } else {
                identifier = "out";
            }

            if (identifier.equals("in")) {
                if (arg == null) {
                    continue;
                }
                tactic = tactic.replaceFirst(" _i", " " + arg.simpleName());
            } else {
                if (arg == null) {
                    continue;
                }
                tactic = tactic.replaceFirst(" _o", " " + arg.simpleName());
            }
        }

        return tactic.substring(0, tactic.length() - 1).replace("_global_", "");
    }

    @Override
    public boolean equals(Object o){
        if(! (o instanceof CoqTactic)) return false;

        CoqTactic tac = (CoqTactic) o;
        return this.sig_no_out_arg.equals(tac.sig_no_out_arg) && this.inputs.equals(tac.inputs) && this.outputs.equals(tac.outputs);
    }

    @Override
    public int hashCode(){
        int hash = sig_no_out_arg.hashCode();
        for (Prop each: inputs) {
            hash += each.hashCode();
        }
        for (Prop each: outputs) {
            hash += each.hashCode();
        }
        hash += this.id;
        return hash;
    }

    public String condensedToString() {
        StringBuilder sb = new StringBuilder(signature);
        for(int i = 0; i < inputs.size(); i++) {
            if (inputs.get(i).type == PROP_TYPE.HYP) {
                int ind = sb.indexOf(" _ ");
                if (ind != -1)
                    sb.replace(ind, ind + 3, " [" + inputs.get(i) + "] ");
            }
        }
        return sb.toString();
    }

    public String toCoqScriptNoArgs() {
        if (this.args.isEmpty()) return this.sigReplaceArgs();

        // for custom tactics
        List<String> args = this.args.stream()
                .map(a -> a.replace("_global_", ""))
                        .collect(Collectors.toList());
        String s = sig_no_out_arg.split(" \\.")[0];
        for (String a: args) {
            String pat;
            if (s.indexOf(" _o") == -1) {
                pat = " _i";
            } else if (s.indexOf(" _i") == -1) {
                pat = " _o";
            } else {
                pat = s.indexOf(" _i") < s.indexOf(" _o") ? " _i" : " _o";
            }
            s = s.replaceFirst(pat, " " + a);
        }
        return s.replace(" , ", ", ");
    }

    public String toCoqScript() {
        return this.sigReplaceArgs();
    }

    public String toString() {
        StringBuilder sb = new StringBuilder(signature + " takes [");
        for(int i = 0; i < inputs.size(); i++) {
            sb.append(inputs.get(i).simpleName()).append(", ");
        }
        sb.append("] and outputs [");
        for(int i = 0; i < outputs.size(); i++) {
            sb.append(outputs.get(i).simpleName()).append(", ");
        }
        sb.append("]\n");
        return sb.toString();
    }

    public String getNonGoalArg(int i) {
        // get i-th non-goal arg
        int j = 0;
        for (Prop arg : this.inputs) {
            if (arg.type.equals(PROP_TYPE.GOAL)) continue;
            if (j == i) return arg.simpleName();
            j++;
        }

        return "";
    }
}
