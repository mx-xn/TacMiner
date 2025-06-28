package main.eval;

import main.config.BmConfig;
import main.encode.*;
import main.proofgraph.*;

// import javax.swing.*;
import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.List;
import java.util.regex.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static main.config.Path.*;
import static main.encode.CoqTactic.serializeArgs;
import static main.enumeration.GraphEnumerator.floydWarshall;
import static main.decode.utils.*;

public class CompressionEval {
    public CompressionEval () {
    }
    static int numProofs = 0; //todo: to be deleted, just for hacks for now.
    public List<ProofGraph> shrinkedGraphs = new ArrayList<>();

    //todo: not sure if this is the best way to store this, but it does prevent recalculation
    public static boolean[][] reachTac;
    public static int[][] pathTac;
//    public static Map<Integer, Integer> create

    public List<String> graphsToScripts() throws Exception {
        throw new Exception ("unimplemented");
    }

    // returns a linearization of the proof graph
    public static String graphToScript(CoqProof proof) {
        ProofGraph pg = proof.pgraph;
        // for each source, construct the list of tactics
        // digraph is a map:
        //   key: a node
        // value: an array of adjacent neighboring nodes

        // construct a hash mapping nodes to their indegrees
        Map<Integer, Integer> indegrees = new HashMap<>();
        List<List<Integer>> neighbors = new ArrayList<>();
        for (int i = 0; i < pg.vertices.size(); i++) {
            indegrees.put(i, 0);
            neighbors.add(new ArrayList<>());
        }

        for (List<ProofGraph.Edge> edgesFromU: pg.simplifiedEdges()) {
            for (ProofGraph.Edge e: edgesFromU) {
                int from = e.u;
                int to = e.v;
                indegrees.put(to, indegrees.get(to) + 1);
                neighbors.get(from).add(to);
            }
        }

        List<Integer> sortedVertices = topoSort(indegrees, neighbors);
        // convert tactics to script
        List<CoqTactic> sortedTactics = sortedVertices.stream().map(id -> pg.vertices.get(id)).collect(Collectors.toList());

        CoqTactic firstTac = sortedTactics.get(0);
        sortedTactics.remove(0);

        String tacticsScript = "";
        try {
            tacticsScript = tacticsToScript(sortedTactics);
        } catch (Exception e) {
            e.printStackTrace();
        }

        String formatted = formatProof(tacticsScript.substring(0, tacticsScript.length() - 1), 1);

        // Hypotheses from the "first" context are in fact from the external section context
        formatted = formatted.replace("c1_", "");

        return firstTac.signature + "\nProof.\n" + formatted + "Qed.";
    }

    public static int countTacticNumArgs(String customTactic) {
        String[] tokens = customTactic.substring(0, customTactic.indexOf(":=")).trim().split(" ");

        // Count the number of arguments
        return Math.max(0, tokens.length - 2);
    }

    public static String formatProof(String tacticScript, int depth) {
        tacticScript = tacticScript.trim();
        StringBuilder pretty = new StringBuilder("");
        for (int t = 0; t < depth; t++) pretty.append("  ");
        for (int t = 0; t < depth - 1; t++) pretty.append("-");
        if (depth > 0) pretty.append(' ');

        while (true) {
            String[] split = {tacticScript};
            {
                int bracketDepth = 0;
                loop:
                for (int i = 0; i < tacticScript.length(); i++) {
                    switch (tacticScript.charAt(i)) {
                        case '[':
                        case '(':
                            bracketDepth++;
                            break;
                        case ')':
                        case ']':
                            bracketDepth--;
                            break;
                        case ';':
                            if (bracketDepth == 0) {
                                split = new String[] {tacticScript.substring(0, i), tacticScript.substring(i+1)};
                                break loop;
                            }
                    }
                }
            }

            if (split.length <= 1) {
                pretty.append(split[0].trim() + ".\n");
                break;
            } else {
                pretty.append(split[0].trim() + ". ");
                split[1] = split[1].trim();
                int last = -1;

                int bracketDepth = 0, goalCount = 0;
                for (int i = 1; i < split[1].length(); i++) {
                    switch (split[1].charAt(i)) {
                        case '[':
                        case '(':
                            bracketDepth++;
                            break;
                        case ')':
                        case ']':
                            bracketDepth--;
                            if (bracketDepth < 0) {
                                goalCount++;
                                if (last == -1) {
                                    last = i;
                                }
                            }
                            break;
                        case '|':
                            if (bracketDepth == 0) {
                                goalCount++;
                                last = i;
                            }
                            break;
                    }
                }

                if (goalCount == 1 || goalCount == 2) {
                    tacticScript = split[1].substring(1, last);
                } else {
                    pretty.append("\n");
                    bracketDepth = 0;
                    last = 1;
                    for (int i = 1; i < split[1].length(); i++) {
                        switch (split[1].charAt(i)) {
                            case '[':
                            case '(':
                                bracketDepth++;
                                break;
                            case ')':
                            case ']':
                                bracketDepth--;
                                if (bracketDepth < 0 && goalCount --> 1) {
                                    pretty.append(formatProof(split[1].substring(last, i), depth + 1));
                                    last = i + 1;
                                }
                                break;
                            case '|':
                                if (bracketDepth == 0 && goalCount --> 1) {
                                    pretty.append(formatProof(split[1].substring(last, i), depth + 1));
                                    last = i + 1;
                                }
                                break;
                        }
                    }
                    break;
                }
            }
        }

        return pretty.toString();
    }

    public static int countProofsLength(String script) {
        int count = 0;

        Pattern pattern = Pattern.compile("(Proof\\..*?Qed\\.|Next Obligation\\..*?Qed\\.)", Pattern.DOTALL);
        Matcher matcher = pattern.matcher(script);
        List<String> proofs = new ArrayList<>();

        while (matcher.find()) {
            proofs.add(matcher.group());
        }


        for (String proof : proofs) {
            Pattern atomicTacPattern = Pattern.compile("\\.\\s|\\.\\n");
            Matcher atomicTacMatcher = atomicTacPattern.matcher(proof.replace("Proof.", "")
                    .replace("Next Obligation.", "")
                    .replace("Qed.", ""));
            while (atomicTacMatcher.find()) {
                count++;
            }
        }

        return count;
    }

    /*
     @inputSize: size of sampling pool
     @numSamples: number of samplings to return
     @sampleSize: size of each sampling
     returns list of sampling, where each sampling contains a list of input ids
     */
    public static List<List<Integer>> getSamplingIDs(int inputSize, int numSamples, int sampleSize) {
        List<List<Integer>> res = new ArrayList<>();
        Random rand = new Random();
        for (int i = 0; i < numSamples; i++) {
            Set<Integer> sample = new HashSet<>();
            while (sample.size() < sampleSize) {
                sample.add(rand.nextInt(inputSize));
            }
            res.add(sample.stream().toList());
        }
        return res;
    }

    /*
     @proofIDs: the proof script to extract
     @filename: proof script file
     */
    public static List<String> getRawProofScriptList(List<Integer> proofIDs, String filename) {
        List<String> proofs = new ArrayList<>();

        Pattern pattern = Pattern.compile("(Proof\\..*?Qed\\.|Next Obligation\\..*?Qed\\.)", Pattern.DOTALL);

        try (BufferedReader br = new BufferedReader(new FileReader(filename))) {
            StringBuilder sb = new StringBuilder();
            String line;
            while ((line = br.readLine()) != null) {
                sb.append(line).append("\n");
            }

            Matcher matcher = pattern.matcher(sb.toString());
            while (matcher.find()) {
                proofs.add(matcher.group());
            }

        } catch (IOException e) {
            e.printStackTrace();
        }

        List<String> res = new ArrayList<>();
        for (int p : proofIDs) {
            res.add(proofs.get(p));
        }

        return res;
    }


    public static String findLongestCommonTactics(String p1, String p2) {
        p1 = p1.replaceAll("Qed.", "")
                .replaceAll("Proof.", "")
                .replaceAll("Next Obligation.", "");
        p2 = p2.replaceAll("Qed.", "")
                .replaceAll("Proof.", "")
                .replaceAll("Next Obligation.", "");
        List<String> tokens1 = Arrays.asList(p1.split("\\. |\\.[\\r\\n]+|- |\\+ |\\* "))
                .stream().map(s -> s.replaceAll("^\\s+|\\s+$", "")).collect(Collectors.toList());
        List<String> tokens2 = Arrays.asList(p2.split("\\. |\\.[\\r\\n]+|- |\\+ |\\* "))
                .stream().map(s -> s.replaceAll("^\\s+|\\s+$", "")).collect(Collectors.toList());

        int[][] dp = new int[tokens1.size() + 1][tokens2.size() + 1];
        int maxLength = 0;
        int startIndex = 0;

        for (int i = 1; i <= tokens1.size(); i++) {
            for (int j = 1; j <= tokens2.size(); j++) {
                if (tokens1.get(i - 1).equals(tokens2.get(j - 1))) {
                    dp[i][j] = dp[i - 1][j - 1] + 1 + (int)tokens1.get(i - 1).chars().filter(ch -> ch == ';').count();
                    if (dp[i][j] > maxLength) {
                        maxLength = dp[i][j];
                        startIndex = i - 1;
                    }
                }
            }
        }

        StringBuilder result = new StringBuilder();
        int len = 1;
        int i = startIndex;
        while (len < maxLength) {
            result.append(tokens1.get(i))
                    .append(". ");
            i++;
            len += (tokens1.get(i).chars().filter(ch -> ch == ';').count() + 1);
        }

        return result.toString().trim();

    }

    public static void writeToBaselineInputFormat(BmConfig config) throws IOException {
        // Regex to match content between "Proof.\n" and "Qed."
        String content = new String(Files.readAllBytes(Paths.get(config.getInputFilename())));
        Pattern pattern = Pattern.compile("(Proof\\..*?(Qed|Defined)\\.|Next Obligation\\..*?Qed\\.)", Pattern.DOTALL);
        Matcher matcher = pattern.matcher(content);

        // Replace the matched content with <placeholder_id>
        StringBuffer newContent = new StringBuffer();
        while (matcher.find()) {
            String matchContent = matcher.group();
            if (matchContent.contains("Proof.")) {
                // replace matchContent with processed string
                String oriStr = matchContent.replace("Proof.", "").replace("Qed.", "");
                boolean defined = false;
                if (oriStr.contains("Defined")) {
                    oriStr = oriStr.replace("Defined.", "");
                    defined = true;
                }
                String replace = formatBaselineProof(oriStr);
                if (defined) {
                    matcher.appendReplacement(newContent, "Proof.\n" + replace + "\nDefined.");
                } else {
                    matcher.appendReplacement(newContent, "Proof.\n" + replace + "\nQed.");
                }
            } else {
                // replace matchContent with processed string
                String oriStr = matchContent.replace("Next Obligation.", "").replace("Qed.", "");
                String replace = formatBaselineProof(oriStr);
                matcher.appendReplacement(newContent, "Next Obligation.\n" + replace + "\nQed.");
            }
        }
        matcher.appendTail(newContent);
        String placeholderContent = newContent.toString();

        List<CoqProof> proofs = Encoder.inputCoqScripts(config.getJsonFilename());

        // for each graph, get the syntactic version
        CompressionEval.numProofs = 0;

        // store the syntactic file
        String[] outputFile = config.getInputFilename().split("/");
        System.out.println("formatted file");
        System.out.println(placeholderContent);
        writeTo(placeholderContent, baselineIntermediatePath + outputFile[0] + "/" + outputFile[outputFile.length - 1]);
    }

    public static String formatBaselineProof(String oriStr) {
        oriStr = oriStr.replaceAll(Pattern.quote("->"), "!>");
        oriStr = oriStr.replaceAll(Pattern.quote("<-"), "<!");
        System.out.println("ori string: " + oriStr);
        List<String> special = Arrays.asList("**** ", "++++ ", "---- ", "*** ", "+++ ", "--- ", "* ", "+ ", "- ", "** ", "++ ", "-- ");
        special = orderSpecialChars(special, oriStr); // innermost first
        oriStr = special.get(special.size() - 1).trim();
        special.remove(special.size() - 1);


        oriStr = oriStr.substring(0, oriStr.length() - 1);
        oriStr = oriStr.replace("\n", " ").replaceAll("\\.\s+", "; [");

        // for each special char c
        for (int i = 0 ; i < special.size(); i++) {
            String sym = special.get(i);
            if (!oriStr.contains(sym)) continue;

            // ignore first occurence
            int start = oriStr.indexOf(sym);
            oriStr = oriStr.replaceFirst(Pattern.quote(sym), "<start>");
            int end = oriStr.indexOf(sym);
            oriStr = oriStr.substring(0, start) + convertBaselineSection(oriStr.substring(start, end), true)
                    + oriStr.substring(end);

            // for each next occurence, replace c with |, add correct number of occurences
            while (oriStr.contains(sym)) {
                start = oriStr.indexOf(sym);
                oriStr = oriStr.replaceFirst(Pattern.quote(sym), "<start>");

                // get the index of next immediate symbol
                int closestInd = Integer.MAX_VALUE;
                for (String c: special) {
                    int ind = oriStr.substring(start).indexOf(c);
                    if (ind == -1) continue;
                    if (ind < closestInd) {
                        closestInd = ind;
                    }
                }

                end = closestInd > oriStr.length() ? oriStr.length(): closestInd + start;
                oriStr = oriStr.substring(0, start) + convertBaselineSection(oriStr.substring(start, end), false)
                        + oriStr.substring(end);
            }
        }

        int count = 0;
        for (char c : oriStr.toCharArray()) {
            if (c == '[') count++;
            else if (c == ']') count--;
        }
        while (count > 0) {
            oriStr += "]";
            count--;
        }

        oriStr += ".";
        oriStr = oriStr.replaceAll(Pattern.quote("!>"), "->");
        oriStr = oriStr.replaceAll(Pattern.quote("<!"), "<-");
        return oriStr.replaceAll("\\[\\s*\\|", "[");
    }

    public static String convertBaselineSection(String s, boolean beginning) {
        if (beginning) {
            s = s.replace("<start>", "");
        } else {
            s = s.replace("<start>", "|");
        }

        s = s.trim();
        if (s.length() > 2 && s.substring(s.length() - 3, s.length()).equals("; [")) {
            s = s.substring(0, s.length() - 3);
        }

        int count = 0;
        for (char c: s.toCharArray()) {
            if (c == '[') count++;
            else if (c == ']') count--;
        }

        String brackets = "";
        while (count > 0) {
            s += "]";
            count--;
        }


        return s;
    }

    // special characters, followed by replace string
    public static List<String> orderSpecialChars(List<String> special, String s)  {
        List<String> res = new ArrayList<>();
        SortedMap<Integer, String> map = new TreeMap();
        char c = 128;
        for (String sp: special) {
            if (!s.contains(sp)) continue;

            // if special char is double, change
            if (sp.length() > 2) {
                s = s.replaceAll(Pattern.quote(sp), Character.toString(c));
                map.put(s.indexOf(c), Character.toString(c));
                System.out.println(sp + ": " + c);
                c++;
            } else {
                map.put(s.indexOf(sp), sp);
            }
        }

        List<Integer> keys = new ArrayList<>(map.keySet());
        System.out.println("ordering:");
        for (int i = keys.size() - 1; i>= 0; i--) {
            System.out.println("key: " + keys.get(i));
            System.out.println("value: " + map.get(keys.get(i)));
            res.add(map.get(keys.get(i)));
        }

        res.add(s);
        System.out.println("inside of order special chars:");
        for (String str: res) {
            System.out.println(str);
        }
        return res;
    }

    public static String findLongestCommonTactics(List<CoqTactic> p1, List<CoqTactic> p2) {
        int maxLen = 1;
        int startIndex1 = -1;
        for (int i = 0; i < p1.size(); i++) {
            for (int j = 0; j < p2.size(); j++) {
                int end1 = i;
                int end2 = j;
                int len = 0;
                boolean stop = false;
                Map<CoqTactic.Prop, CoqTactic.Prop> uniMap1To2 = new HashMap<>();
                // find the longest tactics starting from p1[i] and p2[j]
                while (end1 < p1.size() && end2 < p2.size() && p1.get(end1).signature.equals(p2.get(end2).signature)) {
                    // if signature equals, update unification map
                    List<CoqTactic.Prop> t1Args = serializeArgs(p1.get(end1).gatherArgs(p1.get(end1).signature));
                    List<CoqTactic.Prop> t2Args = serializeArgs(p2.get(end2).gatherArgs(p2.get(end2).signature));

                    for (int k = 0; k < t1Args.size(); k++) {
                        if (uniMap1To2.containsKey(t1Args.get(k))) {
                            if (!uniMap1To2.get(t1Args.get(k)).equals(t2Args.get(k))) {
                                stop = true;
                                break;
                            } // if unification is consistent, just keep going
                        } else {
                            // if new arg is found
                            uniMap1To2.put(t1Args.get(k), t2Args.get(k));
                        }
                    }
                    // if stop, just break
                    if (stop) break;

                    // if unification works, update vars
                    len += (p1.get(end1).signature.chars().filter(ch -> ch == ';').count() + 1);
                    end1++;
                    end2++;
                }
                if (maxLen < len) {
                    maxLen = len;
                    startIndex1 = i;
                }
            }
        }

        if (startIndex1 == -1) return "";

        StringBuilder sb = new StringBuilder();
        int len = 0;
        while (len < maxLen) {
            sb.append(p1.get(startIndex1).toCoqScript())
                    .append(". ");
            len += (p1.get(startIndex1++).signature.chars().filter(ch -> ch == ';').count() + 1);
        }

        return sb.toString().trim();
    }

    /* 
     * Following is for generalized compression: given a proof and a custom tactic, attempt to compress the proof using the tactic.
     * If the tactic is not applicable, the proof is unchanged.
     * In general, this problem (subgraph isomorphism) is NP-Hard, but in practice runs quickly due to frequent pruning.
     */

    public static boolean checkEdgeConsistency(ProofGraph proof, ProofGraph tactic, List<Integer> assn) {
        // All relevant edges in the tactic
        Set<ProofGraph.Edge> tacticEdges = new HashSet<>();
        for (List<ProofGraph.Edge> adj : tactic.adjList) {
            tacticEdges.addAll(adj);
        }

        // All relevant edges in the proof, "normalized"
        Set<ProofGraph.Edge> proofEdges = new HashSet<>();
        for (int i = 0; i < proof.vertices.size(); i++) {
            int u = assn.get(i);
            if (u < 0) continue;
            for (int j = 0; j < proof.adjList.get(i).size(); j++) {
                ProofGraph.Edge origEdge = proof.adjList.get(i).get(j);
                int v = assn.get(origEdge.v);
                if (v < 0) continue;
                proofEdges.add(new ProofGraph.Edge(u, v, origEdge.fromPos, origEdge.toPos));
            }
        }


        boolean consistent = false;
        if (tacticEdges.equals(proofEdges)) consistent = true;

        // if tacticEdges are subset of proofEdges
        for (ProofGraph.Edge e: tacticEdges) {
            if (consistent) break;
            if (!proofEdges.contains(e))
                return false;
        }

        // need to check collapsibility as well using floyd warshall
        int numV = proof.vertices.size();
        boolean[][] reach = new boolean[numV][numV];
        int[][] path = new int[numV][numV];
        floydWarshall(reach, path, proof);

        int numTacV = tactic.vertices.size();
        for (int u = 0; u < numTacV; u++) {
            for (int v = 0; v < numTacV; v++) {
                // assn: proof v -> tactic v
                int uG = assn.indexOf(u);
                int vG = assn.indexOf(v);
                if (CompressionEval.reachTac[u][v] && CompressionEval.pathTac[u][v] != path[uG][vG]) {
                    return false;
                }
            }
        }

        return true;
    }

    // assn: map from proof vertex to tactic vertex
    // assned: added tactic vertex
    public static List<Integer> searchSubgraph(ProofGraph proof, ProofGraph tactic, List<Integer> assn, Set<Integer> assned) {
        if (assn.size() == proof.vertices.size()) {
            if (assned.size() < tactic.vertices.size()) return null;
            // Verify edges
            if (checkEdgeConsistency(proof, tactic, assn)) {
                return assn;
            }

            return null;
        }

        if (tactic == null) return null;

        int index = assn.size();
        for (int k = 0; k < tactic.vertices.size(); k++) {
            if (!assned.contains(k)) {
                // Prune based on signature
                if (tactic.vertices.get(k).sig_no_out_arg.equals(proof.vertices.get(index).sig_no_out_arg)) {
                    // try to match tactics[k], proofs[assn.size()]
                    // if tactics[k] matches, add that to assn and assned
                    assn.add(k);
                    assned.add(k);
                    List<Integer> match = searchSubgraph(proof, tactic, assn, assned);
                    if (match != null) {
                        return match;
                    }
                    assn.remove(assn.size() - 1); //removeLast();
                    assned.remove(k);
                }
            }
        }
        
        assn.add(-1);
        List<Integer> match = searchSubgraph(proof, tactic, assn, assned);
        if (match != null)
            return match;
        assn.remove(assn.size() - 1); //removeLast();

        return null;
    }

    public static CoqTactic populateCustom(CoqProof orig, CoqProof customTac, List<Integer> match) {
        List<CoqTactic> correspTacs = new ArrayList<>(customTac.tactics.size());
        for(int i = 0; i < customTac.tactics.size(); i++) correspTacs.add(null);
        for(int i = 0; i < match.size(); i++) {
            if (match.get(i) >= 0) {
                if (match.get(i) >= correspTacs.size()) {
                    System.out.println();
                }
                correspTacs.set(match.get(i), orig.tactics.get(i));
            }
        }

        Set<CoqTactic.Prop> inSet = new LinkedHashSet<>();
        Set<CoqTactic.Prop> outSet = new LinkedHashSet<>();

        for (CoqTactic tactic : correspTacs) {
            inSet.addAll(tactic.inputs);
            outSet.addAll(tactic.outputs);
        }

        List<String> inArgs = new ArrayList<>();
        List<String> outArgs = new ArrayList<>();
        Map<CoqTactic.Prop, List<CoqTactic.Prop>> goalMap = new HashMap<>();

        for (CoqTactic tactic: correspTacs) {
            List<CoqTactic.Prop> inputGoal = tactic.inputs.stream().filter(p -> p.type.equals(CoqTactic.PROP_TYPE.GOAL)).toList();
            if (inputGoal.isEmpty()) continue;
            goalMap.put(inputGoal.get(0), tactic.outputs.stream().filter(g -> g.type.equals(CoqTactic.PROP_TYPE.GOAL)).toList());
        }

        int numPrintedOuts = 0;
        for (CoqTactic tactic : correspTacs) {
            for (CoqTactic.Prop in : tactic.inputs) {
                if (in.type == CoqTactic.PROP_TYPE.GOAL) {
                    if (!outSet.contains(in)) {
                        inArgs.add(in.toString());
                    }
                }
            }

            int numEffectiveOutput = 0;
            String copy = new String(tactic.sig_no_out_arg);
            while (copy.contains(" _o")) {
                copy = copy.replaceFirst(" _o", "***");
                numEffectiveOutput++;
            }
            for (CoqTactic.Prop out : tactic.outputs) {
                if (out.type == CoqTactic.PROP_TYPE.HYP) {
                    if (numEffectiveOutput > 0) {
                        // swap first element with curr element
                        if (outArgs.isEmpty()) outArgs.add(out.toString());
                        else {
                            // get first swapable hyp
                            int add = numPrintedOuts;
                            int swapInd = -1;
                            for (int i = 0; i < outArgs.size(); i++) {
                                if (outArgs.get(i).contains("_goal")) continue;
                                if (add-- != 0) continue;
                                swapInd = i;
                                break;
                            }
                            if (swapInd == -1) outArgs.add(out.toString());
                            else {
                                outArgs.add(outArgs.get(swapInd));
                                outArgs.set(swapInd, out.toString());
                            }
                        }
                        numEffectiveOutput--;
                        numPrintedOuts++;
                    } else {
                        outArgs.add(out.toString());
                    }
                } else if (out.type == CoqTactic.PROP_TYPE.GOAL) {
                    List<CoqTactic.Prop> goalsToAdd = goalMap.containsKey(out) ? goalMap.get(out) : Arrays.asList(out);
                    List<String> before;
                    List<String> after = new ArrayList<>();
                    if (outArgs.contains(out.toString())) {
                        // replace
                        int indexOfReplace = outArgs.indexOf(out.toString());
                        before = new ArrayList<>(outArgs.subList(0, indexOfReplace));
                        after = new ArrayList<>(outArgs.subList(indexOfReplace + 1, outArgs.size()));
                    } else {
                        // append
                        before = new ArrayList<>(outArgs);
                    }

                    for (CoqTactic.Prop goal: goalsToAdd) {
                        before.add(goal.toString());
                    }
                    before.addAll(after);
                    outArgs = before;
                }
            }
        }

        List<String> genericArgs = Arrays.stream(customTac.lemma_name.split(" ")).toList();
        String actualSig = customTac.raw_string.split(" := ")[0];
        List<String> actualArgs = Arrays.stream(actualSig.split(" ")).toList();

        genericArgs = genericArgs.subList(1, genericArgs.size());
        actualArgs = actualArgs.subList(1, actualArgs.size());

        List<String> actualInArgs = new ArrayList<>();
        Set<String> remove = new HashSet<>();
        List<String> orderedArgs = new ArrayList<>();
        for (int i = 0; i < actualArgs.size(); i++) {
            if (genericArgs.get(i).equals("_i")) {
                actualInArgs.add(actualArgs.get(i));
                orderedArgs.add(null);
            }
        }

        for (int i = 0; i < customTac.tactics.size(); i++) {
            int numEffectiveInput = 0;
            String copy = customTac.tactics.get(i).sig_no_out_arg;
            while (copy.contains(" _i")) {
                copy = copy.replaceFirst(" _i", "***");
                numEffectiveInput++;
            }
            for (int a = 0; a < customTac.tactics.get(i).inputs.size(); a++) {
                CoqTactic.Prop inA = customTac.tactics.get(i).inputs.get(a);
                if (inA.type.equals(CoqTactic.PROP_TYPE.HYP)) {
                    numEffectiveInput--;
                    if (remove.contains(inA.simpleName())) continue;
                    if (actualInArgs.contains(inA.simpleName())) {
                        remove.add(inA.simpleName());

                        // we need to add the args in order
                        orderedArgs.set(actualInArgs.indexOf(inA.simpleName()), correspTacs.get(i).inputs.get(a).toString());
                    }
                }
                if (numEffectiveInput == 0) break;
            }
        }
        for (String a: orderedArgs) inArgs.add(a);

        // get a map from H to in / out
        // get another map from H to
        CoqTactic custom = new CoqTactic(customTac.lemma_name, customTac.lemma_name, inArgs, outArgs);
        return custom;
    }

    public static CoqProof compressProof(CoqProof orig, CoqProof customTac, int p) {
        if (customTac.lemma_name.equals("custom53")) {
            System.out.println();
        }
        customTac.pgraph = new ProofGraph(new ArrayList<>(customTac.tactics));
        if (orig.pgraph == null) orig.pgraph = new ProofGraph(orig.tactics);

        // if run on entire corpus, we can help the search
        List<Integer> match;
        if (customTac.matches.containsKey(p)) {
            if (customTac.matches.get(p).isEmpty()) return orig;
            // assn: map from proof vertex to tactic vertex
            List<Integer> assn = new ArrayList<>();
            List<Integer> tacMap = customTac.matches.get(p);
            // current gVID's that should be included
            List<Integer> gVIDs = new ArrayList<>();
            for (int i = 0; i < customTac.tactics.size(); i++) {
                gVIDs.add(tacMap.get(i));
            }
            for (int pID = 0; pID < orig.tactics.size(); pID++) {
                int tID = tacMap.indexOf(pID);
                if (gVIDs.contains(pID)) {
                    assn.add(tID);
                } else {
                    assn.add(-1);
                }
            }
            // assned: added tactic vertex
            Set<Integer> assned = new HashSet<>(IntStream.range(0, customTac.tactics.size()).boxed().collect(Collectors.toSet()));
            match = searchSubgraph(orig.pgraph, customTac.pgraph, assn, assned);
        } else {
            // if match does not contain p
            // if p is in training index: just do not search at all
            // if p not in trianing index: search
            boolean skip = false;
            if (orig.lemma_name.equals("transl_exitexpr_charact") && customTac.tactics.size() == 10) {
                skip = true;
                for (int i = 2; i < customTac.tactics.size(); i++) {
                    if (!customTac.tactics.get(i).sig_no_out_arg.contains("eauto with rtlg")) {
                        skip = false;
                        break;
                    }
                }
            }
            if (skip) match = null;
            else match = searchSubgraph(orig.pgraph, customTac.pgraph, new ArrayList<>(), new HashSet<>());
        }
        if (match == null) {
            return orig;
        }

        // get reachable of tactic and orig
        CoqTactic customCompressed = populateCustom(orig, customTac, match);

        CoqProof compressed = new CoqProof(orig);
        compressed.tactics.clear();

        int id = 0;
        // 0, 1!, 2, 3, !4, !5, 6, 7, 8
        // matches.get(p): 3, 7, 8
        // 0, 2, 3, 6, 7, 8
        // 0, 1, 2, 3, 4, 5
        // new matches.get(p): 2, 4, 5
        List<Integer> updatedTacMatches = new ArrayList<>();
        boolean added = false;
        for (int i = 0; i < match.size(); i++) {
            if (match.get(i) < 0) {
                // if gets here, either no match at all, or match but not the last round
                CoqTactic t = new CoqTactic(orig.tactics.get(i));
                if (customTac.matches.get(p) == null)
                    System.out.println();
                if (customTac.matches.containsKey(p) && customTac.matches.get(p).contains(i)) {
                    // if match but not last round, add curr index
                    updatedTacMatches.add(id);
                }
                t.id = id++;
                compressed.tactics.add(t);
            } else {
                if (!added) {
                    customCompressed.id = id++;
                    compressed.tactics.add(customCompressed);
                    added = true;
                }
            }
            // gets here, match last round, whatever goes after this should have its index -1 in tactic.matches.get(p)
        }
        if (customTac.matches.containsKey(p))
            customTac.matches.put(p, updatedTacMatches);


        compressed.pgraph = null; // Force graph reconstruction
        try {
            compressed.initProofGraph();
            for (int i = 0; i < compressed.pgraph.vertices.size(); i++) {
                compressed.pgraph.checkCycle(i, new HashSet<>());
            }
        } catch (Exception e) {
            System.out.println("init proof " + p + " in compressProof" + e.getMessage());
        }
        return compressProof(compressed, customTac, p);
    }
    
    public static Set<CoqProof> getCompressedTactics(List<CoqProof> tactics) {
        tactics.sort((o1, o2) -> Integer.compare(o2.tactics.size(), o1.tactics.size()));

        Set<CoqProof> compressedTacs = new HashSet<>();
        Set<Integer> compressed = new HashSet<>();
        for (int i = 0; i < tactics.size(); i++) {
            for (int j = tactics.size() - 1; j > i; j--) {
                CoqProof child = tactics.get(j);
                CoqProof parent = tactics.get(i);

                if (child.tactics.size() == parent.tactics.size()) break;

                // get signature mapping, prune if sig in child \notin sig in parent
                Map<String, Integer> childSigCounts = child.getSigCount();
                Map<String, Integer> parentSigCounts = parent.getSigCount();

                boolean skip = false;
                for (Map.Entry<String, Integer> childSigCount: childSigCounts.entrySet()) {
                    // if parent sig contains child sig, p_count has to >= c_count
                    if (!parentSigCounts.containsKey(childSigCount.getKey()) || parentSigCounts.get(childSigCount.getKey()) < childSigCount.getValue()) {
                        skip = true;
                        break;
                    }
                }

                if (skip) continue;

                // try to compress parent, add compressed parent
            }
        }

        // forall uncompressed tactics, add to result
        for (CoqProof tac: tactics) {
            if (!compressed.contains(tac))
                compressedTacs.add(tac);
        }

        return compressedTacs;
    }
    
    public static int compressExtractedTactic(CoqProof tactic, List<CoqProof> libTacs) {
        libTacs = libTacs.stream().filter(t -> t.tactics.size() < tactic.tactics.size()).collect(Collectors.toList());
        libTacs.sort((t1, t2) -> Integer.compare(t2.tactics.size(), t1.tactics.size()));

        Map<String, Integer> parentSigCounts = tactic.getSigCount();
        for (CoqProof smallerTac: libTacs) {
            Map<String, Integer> childSigCounts = smallerTac.getSigCount();

            boolean skip = false;
            for (Map.Entry<String, Integer> childSigCount: childSigCounts.entrySet()) {
                // if parent sig contains child sig, p_count has to >= c_count
                if (!parentSigCounts.containsKey(childSigCount.getKey()) || parentSigCounts.get(childSigCount.getKey()) < childSigCount.getValue()) {
                    skip = true;
                    break;
                }
            }
            
            // if skip current tactic, continue, otherwise, try search for subgraph
            if (skip) continue;
            
            // if current tactic can be compressed using smallerTac, break out of the loop
            List<Integer> match = searchSubgraph(tactic.pgraph, smallerTac.pgraph, new ArrayList<>(), new HashSet<>());
            if (match != null && !match.isEmpty()) {
                return tactic.tactics.size() - smallerTac.tactics.size() + 1;
            }
        }

        return tactic.tactics.size();
    }
    public static List<List<CoqProof>> compressLibTacs(CoqProof tactic, List<CoqProof> libTacs) {
        int decrease = 0;
        // for each libTac that can be compressed by tactic, decrease libTac size by tactic.size - 1
        Map<String, Integer> childSigCounts = tactic.getSigCount();
        boolean compressible = false;
        List<CoqProof> compressedTactics = new ArrayList<>();
        for (CoqProof largerTac: libTacs) {
            if (largerTac.tactics.size() <= tactic.tactics.size()) {
                compressedTactics.add(largerTac);
                continue;
            }
            Map<String, Integer> parentSigCounts = largerTac.getSigCount();

            boolean skip = false;
            for (Map.Entry<String, Integer> childSigCount: childSigCounts.entrySet()) {
                // if parent sig contains child sig, p_count has to >= c_count
                if (!parentSigCounts.containsKey(childSigCount.getKey()) || parentSigCounts.get(childSigCount.getKey()) < childSigCount.getValue()) {
                    skip = true;
                    break;
                }
            }

            // if skip current tactic, continue, otherwise, try search for subgraph
            if (skip) {
                compressedTactics.add(largerTac);
                continue;
            }

            // if current tactic can be compressed using smallerTac, try compress the tactic
            CoqProof compressedTac = compressProof(largerTac, tactic, -1);
            compressedTactics.add(compressedTac);
            if (!compressedTac.equals(largerTac)) {
                compressible = true;
            }
        }
        if (compressible) {
            return Arrays.asList(libTacs, compressedTactics);
        }
        return Arrays.asList(libTacs);
    }

}
