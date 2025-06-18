package main.encode;

import java.util.*;
import java.util.stream.Collectors;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Multimap;

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
//    public boolean isCustom = false;
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
//        this.args = this.gatherArgs(this.sig_no_out_arg).keySet().stream().filter(p -> p != null).map(p -> p.simpleName()).toList();
//=======
//        this.args = new ArrayList<>();
//        this.getArgList(this.sig_no_out_arg, this.args, new ArrayList<>());
//>>>>>>> bc4a1285d06941f337efe7bc9309710cd628d35c
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
//=======
//    public Map<Prop, String> getArgList(String signature, List<String> argList, List<String> in_outList) {
//>>>>>>> bc4a1285d06941f337efe7bc9309710cd628d35c
        Queue<Prop> inputHyps = new LinkedList<>(this.inputs.stream().filter(in -> in.type.equals(PROP_TYPE.HYP)).collect(Collectors.toList()));
        Queue<Prop> outputHyps = new LinkedList<>(this.outputs.stream().filter(in -> in.type.equals(PROP_TYPE.HYP)).collect(Collectors.toList()));
        Queue<Integer> outArgIndices = new LinkedList<>();
        Queue<Integer> inArgIndices = new LinkedList<>();
        String sig = signature.split(" \\.")[0] + " ";
//        System.out.println("curr sig is " + this.signature);
        while (sig.indexOf(" _o") != -1) {
            outArgIndices.add(sig.indexOf(" _o"));
            sig = sig.replaceFirst(" _o", " ++");
        }
//        System.out.println("outArgIndices: " + outArgIndices.toString());

        while (sig.indexOf(" _i") != -1) {
            inArgIndices.add(sig.indexOf(" _i"));
            sig = sig.replaceFirst(" _i", " ++");
        }
//        System.out.println("inArgIndices: " + inArgIndices.toString());
    //    System.out.println("in-hyps: " + inputHyps.stream().map(x -> x.name).collect(Collectors.toList()));
    //    System.out.println("out-hyps: " + outputHyps.stream().map(x -> x.name).collect(Collectors.toList()));

        Map<String, Prop> res = new LinkedHashMap<>();
        int order = 0;
        while (!outArgIndices.isEmpty() || !inArgIndices.isEmpty()) {
            boolean addInputArg = false;
            if (outArgIndices.isEmpty() ||
                    (!inArgIndices.isEmpty() && inArgIndices.peek() < outArgIndices.peek())) {
//                System.out.println(inArgIndices.peek() + " < " + outArgIndices.peek());
                addInputArg = true;
            }

            // if both indices are not empty, compare them
            if (addInputArg) {
                Prop currP = inputHyps.poll();
                res.put("in" + (order++), currP);
//                if (!res.containsKey(currP)) res.put(currP, new ArrayList<>());
//                res.get(currP).add("in");
                inArgIndices.poll();
            } else {
//                System.out.println("polling from outHyps " + outputHyps.size());
                Prop currP = outputHyps.poll();
                res.put("out" + (order++), currP);
//                if (!res.containsKey(currP)) res.put(currP, new ArrayList<>());
//                res.get(currP).add("out");
//=======
//                if (!inputHyps.isEmpty()) {
//                    argList.add(inputHyps.peek().simpleName());
//                    in_outList.add("in");
//                }
//                res.put(inputHyps.poll(), "in");
//                inArgIndices.poll();
//            } else {
//                if (!outputHyps.isEmpty()) {
//                    argList.add(outputHyps.peek().simpleName());
//                    in_outList.add("out");
//                }
//                res.put(outputHyps.poll(), "out");
//>>>>>>> bc4a1285d06941f337efe7bc9309710cd628d35c
                outArgIndices.poll();
            }
        }
        return res;
    }

    // return key=arg obj, val="in" or "out"
//    public Map<Prop, String> gatherArgs(String signature) {
//        return getArgList(signature, new ArrayList<>(), new ArrayList<>());
//    }

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
//        for (Prop arg: argMap.keySet()) {
//            for (String identifier: argMap.get(arg)) {
//                if (identifier.equals("in")) {
//                    if (arg == null) {
//                        continue;
//                    }
//                    tactic = tactic.replaceFirst(" _i", " " + arg.simpleName());
//                } else {
//                    if (arg == null) {
//                        continue;
//                    }
//                    tactic = tactic.replaceFirst(" _o", " " + arg.simpleName());
//                }
//    }
//=======
//        List<String> argMap = new ArrayList<>();
//        List<String> in_outMap = new ArrayList<>();
//        this.getArgList(this.signature, argMap, in_outMap);
//        for (int t = 0; t < argMap.size(); t++) {
//            if (in_outMap.get(t).equals("in")) {
//                tactic = tactic.replaceFirst("_i ", argMap.get(t) + " ").replaceFirst("_global_", "");
//            } else {
//                tactic = tactic.replaceFirst("_o ", argMap.get(t) + " ");
//    }
//>>>>>>> bc4a1285d06941f337efe7bc9309710cd628d35c

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

        // if signature contains ";" just print out the whole thing
//        if (this.signature.contains(";"))
//            sigName = "composite";

        // for custom tactics
//        StringBuilder sb = new StringBuilder(this.sig_no_out_arg.split(" \\.")[0].replaceAll("_o", "")
//                .replaceAll("_i", "").trim());
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
//        sb.append(" ").append(String.join(" ",
//                this.args.stream()
//                        .map(a -> a.replace("_global_", "global_")
//                                .split("_", 2)[1]).collect(Collectors.toList())));
    }

    public String toCoqScript() {
//        if (!this.signature.startsWith("custom")) {
//            return this.sigReplaceArgs();
//        }
        return this.sigReplaceArgs();

        // if signature contains ";" just print out the whole thing
//        if (this.signature.contains(";"))
//            sigName = "composite";

        // for custom tactics
//        StringBuilder sb = new StringBuilder(signature.split(" \\.")[0]);
//        sb.append(" ").append(String.join(" ", this.args.stream().map(a -> a.replace("_global_", "")).collect(Collectors.toList())));

//        switch (sigName) {
////            case "induction": break;
//            case "simpl":
//            case "intuition":
//            case "congruence":
//            case "tauto":
//            case "exfalso":
//            case "omege":
//            case "split":
//            case "lia":
//            case "extlia":
//            case "constructor":
//            case "eauto":
//                break;
//
//            case "destruct":
//            case "intros":
//            case "exploit":
//            case "rewrite":
//            case "assert":
//            case "composite":
//                // replace all the "_" with non-goal args
//                int i = 0;
//                while (sb.indexOf("_") != -1) {
//                    int index = sb.indexOf("_");
//                    sb.replace(index, index + 1, getNonGoalArg(i++));
//                }
//                break;
//            default:
//                //if (this.args.isEmpty())
//                sb.append(this.sigReplaceArgs());
//                if (!this.args.isEmpty()) {
//                    sb = new StringBuilder(sigName);
//                    sb.append(" ").append(String.join(" ", this.args));
//                }
//        }
//        sb.append(".");
//        return sb.toString();
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
