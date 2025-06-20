package main.decode;
import main.encode.CoqTactic;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

public class utils {
    public static Map<String, String> gatherCompositeArgs(List<CoqTactic> compTactic) {
        // given a list of atomic tactics in a composite tactic, returns the list of arguments
        List<String> args = new ArrayList<>();
        Map<String, String> res = new LinkedHashMap<>();  // key: arg names, val: "in" or "out"
        for (CoqTactic tactic: compTactic) {
            if (tactic == null) continue;
            // System.out.println("gather args for " + tactic.toCoqScript());
            // add the args for all the tactics
            for (Map.Entry<String, CoqTactic.Prop> argEnt: tactic.gatherArgs(tactic.signature).entrySet()) {
                CoqTactic.Prop arg = argEnt.getValue();
                if (arg == null) {
                    System.out.println();
                }
                if (args.contains(arg.simpleName())) continue;

                String type = argEnt.getKey();
                if (type.contains("in")) {
                    res.put(arg.simpleName(), "_i");
                } else {
                    res.put(arg.simpleName(), "_o");
                }
                args.add(arg.simpleName());
            }
        }
        return res;
    }
    private static int findNthPipeIndex(String input, String afterPattern, int startIndex, String tactic, int n) {
        int indexOfAfter = startIndex + afterPattern.length(); 

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

                branch++;
                if (parentOut.equals(inputGoalProp)) {
                    if (numSkips > 0) {
                        numSkips--;
                        break;
                    }

                    // find the branch-th slot
                    int parentIndex = insertIndexMap.get(parentCandidate);
                    int insertInd = findNthPipeIndex(script, parentCandidate.toCoqScript(), parentIndex, tactic.toCoqScript(), branch) - 1;
                    if (script.substring(0, insertInd).endsWith("; []")) insertInd--;
                    return insertInd;
                }
            }
        }

        if (script.indexOf("[]") != -1) return script.indexOf("[]") + 1;
        return -1;
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

    // for io ----------------------------------------------------
    public static void writeTo(String output, String fileName)
            throws IOException {
        File file = new File(fileName);
        file.getParentFile().mkdirs(); // Create parent directories if they don't exist
        BufferedWriter writer = new BufferedWriter(new FileWriter(file));
        writer.write(output);
        writer.close();
    }

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

}
