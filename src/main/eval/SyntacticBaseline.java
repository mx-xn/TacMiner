package main.eval;

import main.config.BmConfig;
import main.encode.CoqProof;
import main.encode.CoqTactic;
import main.encode.Encoder;
import main.lib_assembler.LibAssemblerBaseline;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static main.config.Path.*;
import static main.lib_assembler.LibAssemblerBaseline.assembleLibraryBaseline;
import static main.decode.utils.writeTo;

public class SyntacticBaseline {
    public static class BaselineProof {
        public List<String> cleanTokens;
        public List<String> completeTokens;
        public List<String> cleanCompleteTokens;
        public List<List<String>> args;
        public String name = "";

        public BaselineProof(List<String> cleanTokens, List<String> completeTokens, List<List<String>> args) {
            this.cleanTokens = cleanTokens;
            this.completeTokens = completeTokens;
            this.cleanCompleteTokens = getCleanCompleteTokens();
            this.args = args;
        }

        public BaselineProof(List<String> cleanTokens, List<String> completeTokens, List<String> cleanCompleteTokens, List<List<String>> args) {
            this.cleanTokens = cleanTokens;
            this.completeTokens = completeTokens;
            this.cleanCompleteTokens = cleanCompleteTokens;
            this.args = args;
        }

        public BaselineProof(BaselineProof copy) {
            this.cleanTokens = new ArrayList<>(copy.cleanTokens);
            this.completeTokens = new ArrayList<>(copy.completeTokens);
            this.cleanCompleteTokens = new ArrayList<>(copy.cleanCompleteTokens);
            this.args = new ArrayList<>(copy.args);
            this.name = copy.name;
        }

        public List<String> getCleanCompleteTokens() {
            String start = completeTokens.get(0);
            if (start.substring(0, 3).equals("; [")) {
                start = start.substring(3);
            }
            StringBuilder completeStr = new StringBuilder(start);

            List<String> res = new ArrayList<>(Arrays.asList(start));
            for (int i = 1; i < this.size() - 1; i++) {
                res.add(this.completeTokens.get(i));
                completeStr.append(this.completeTokens.get(i));
            }

            if (this.size() == 1) return res;

            String end = new String(completeTokens.get(this.size() - 1));
            while (end.charAt(end.length() - 1) == ']' || end.charAt(end.length() - 1) == '|' || end.charAt(end.length() - 1) == '.') {
                end = end.substring(0, end.length() - 1).trim();
            }

            res.add(end);
            return res;
        }

        // replace current proof start with start to tactic
        public void compressSection(int start, BaselineProof tactic, List<List<String>> args) {
            this.args.subList(start, start + tactic.size()).clear();
            List<String> newArgs = new ArrayList<>();
            for (List<String> as: args) {
                for (String a: as) {
                    if (!newArgs.contains(a))
                        newArgs.add(a);
                }
            }
            this.args.add(start, newArgs);

            this.cleanTokens.subList(start, start + tactic.size()).clear();
            this.cleanTokens.add(start, tactic.name);

            this.completeTokens.subList(start, start + tactic.size()).clear();
            this.completeTokens.add(start, tactic.name + " " + String.join(" ", newArgs));

            this.cleanCompleteTokens.subList(start, start + tactic.size()).clear();
            this.cleanCompleteTokens.add(start, tactic.name);
        }

        public void compress(BaselineProof tactic) {
            BaselineProof p = new BaselineProof(this);
            // if clean complete token of tactic is not a substring, cannot compress
            if (!String.join("", p.cleanCompleteTokens).contains(String.join("", tactic.cleanCompleteTokens))) return;

            // if unification does not work, cannot compress
            String first = tactic.cleanTokens.get(0);
            int i = 0;
            int indexDecrease = 0;

            while (p.cleanTokens.subList(i, p.cleanTokens.size()).contains(first)) {
                // check if remaining is also a match
                int startIndex = p.cleanTokens.subList(i, p.cleanTokens.size()).indexOf(first) + i;
                if (startIndex + tactic.size() > p.size()) break;
                BaselineProof match = p.getSubproof(startIndex, tactic.size());
                if (match.cleanCompleteTokens.equals(tactic.cleanCompleteTokens)) {
                    // if remaining a match, try to unify the arguments, update i -> i + tactic.size
                    if (canUnify(match.args, tactic.args)) {
                        // replace
                        this.compressSection(startIndex - indexDecrease, tactic, match.args);
                        i = startIndex + tactic.size();
                        indexDecrease += (tactic.size() - 1);
                        continue;
                    }
                }

                // if remaining not a match, or unification does not work, keep going
                i++;
            }
        }

        @Override
        public boolean equals(Object o){
            if(! (o instanceof BaselineProof)) return false;

            BaselineProof proof = (BaselineProof) o;
            return this.cleanCompleteTokens.equals(proof.cleanCompleteTokens) && this.args.equals(proof.args);
        }

        public int size() {
            return this.cleanTokens.size();
        }

        public BaselineProof getSubproof(int start, int size) {
            List<String> cleanTokens = new ArrayList<>(this.cleanTokens.subList(start, start + size));
            List<String> completeTokens = new ArrayList<>(this.completeTokens.subList(start, start + size));
            List<String> cleanCompleteTokens = new ArrayList<>(this.cleanCompleteTokens.subList(start, start + size));
            List<List<String>> args = new ArrayList<>(this.args.subList(start, start + size));

            return new BaselineProof(cleanTokens, completeTokens, cleanCompleteTokens, args);
        }

        public String prettyPrint() {
            return String.join("; ", this.cleanCompleteTokens);
        }

        public String cusTacticScript() {
            StringBuilder sb = new StringBuilder("Ltac ");
            sb.append(this.name).append(" ");
            List<String> allArgs = new ArrayList<>();
            for (List<String> a: this.args) {
                allArgs.addAll(a);
            }
            sb.append(String.join(" ", allArgs.stream().distinct().toList()))
                    .append(" := ");

            List<String> tokens = new ArrayList<>();
            for (int t = 0; t < this.cleanCompleteTokens.size(); t++) {
                String copy = new String(this.cleanCompleteTokens.get(t));
                int i = 0;
                while (copy.contains(" _i") || copy.contains(" _o")) {
                    int indexI = copy.contains(" _i") ? copy.indexOf(" _i") : Integer.MAX_VALUE;
                    int indexO = copy.contains(" _o") ? copy.indexOf(" _o") : Integer.MAX_VALUE;
                    if (indexI < indexO) {
                        copy = copy.replaceFirst(" _i", " " + this.args.get(t).get(i++));
                    } else {
                        copy = copy.replaceFirst(" _o", " " + this.args.get(t).get(i++));
                    }
                }
                tokens.add(copy);
            }
            sb.append(String.join("; ", tokens)).append(".");
            return sb.toString();
        }
    }

    public static void baselineExtractRaw(BmConfig config, List<CoqProof> coqProofs) throws IOException {
        // extract list of proof strings from the syntactic baseline input file
        System.out.println("Extracting tactics using baseline (Peano) for Topic: " + config.topic);
        List<String> rawProofs = retrieveProofStringsFromFile(config.getInputFilename());
        List<String> proofs = rawProofs.stream().map(p -> p.replaceAll("[\\s]{2,}", " ")).toList();

        // for each proof string, get the preprocessed proof string, also the arg maps and tokenized preprocessed proofs
        coqProofs = coqProofs.stream().filter(p -> p.tactics.size() >= 1).collect(Collectors.toList());
        List<Integer> trainingProofIndices = Encoder.getTrainingProofIndices(config, coqProofs);
        List<List<List<String>>> proofsArgs = new ArrayList<>();
        List<BaselineProof> baselineProofs = new ArrayList<>();
        int id = 0;
        for (String p: proofs) {
            List<String> genericProofTokens = new ArrayList<>();
            List<String> genericCompleteTokens = new ArrayList<>();
            List<List<String>> args = new ArrayList<>();

            List<String> completeProofTokens = tokenizeRawProof(p);
            getGenericSigProof(completeProofTokens, coqProofs.get(id++), genericProofTokens, genericCompleteTokens, args);

            proofsArgs.add(args);
            baselineProofs.add(new BaselineProof(genericProofTokens, completeProofTokens, genericCompleteTokens, args));
        }

        // for each pair of the proofs, extract best tactics
        List<BaselineProof> customTacs = new ArrayList<>();
        for (int k = 0; k < trainingProofIndices.size(); k++) {
            for (int l = k + 1; l < trainingProofIndices.size(); l++) {
                // extract between proof i and j
                int i = trainingProofIndices.get(k);
                int j = trainingProofIndices.get(l);
                BaselineProof tactic = longestCommonTactics(baselineProofs.get(i), baselineProofs.get(j));

                if (tactic != null) {
                    boolean stop = false;
                    for (String t: tactic.cleanCompleteTokens) {
                        if (t.contains("destr_t x") || t.contains("caseEq ( map_vars map)!i")) {
                            stop = true;
                            break;
                        }
                    }
                    if (stop)
                        continue;
                    if (!customTacs.contains(tactic)) {
                        tactic.name = "custom_tac" + customTacs.size();
                        customTacs.add(tactic);
                    }
                }
            }
        }

        // try to assemble the library
        System.out.println("assembling library ... ");
        LibAssemblerBaseline.LibraryBaseline libGreedy = assembleLibraryBaseline(new ArrayList<>(baselineProofs), new ArrayList<>(customTacs),
                LibAssemblerBaseline.AssemblyType.GREEDY, trainingProofIndices);

        libGreedy.validCheck(rawProofs, coqProofs, baselineProofs, config);
        if (config.mode != BmConfig.Mode.ENUMERATION_SPLIT) {
            // if is not in training mode, running RQ1 
            if (config.training) {
                writeTo(libGreedy.printTactics(), evalPath + RQ2 + "baseline/tactics/" + config.topic + ".txt");
                writeTo(libGreedy.printCompressionRate(), evalPath + RQ2 + "baseline/" + config.topic + ".csv");
            } else {
                writeTo(libGreedy.printTactics(), evalPath + RQ1 + "baseline/tactics/" + config.topic + ".txt");
                writeTo(libGreedy.printTacticsStats(), evalPath + RQ1 + "baseline/" + config.topic + ".csv");
            }
        }
        System.out.println("finished assembling tactic-library for: " + config.topic);
    }

    // returns the [start(incl), size] of proofs1
    public static BaselineProof longestCommonTactics(BaselineProof p1, BaselineProof p2) {
        int bestStart = -1;
        int bestSize = 0;
        // get the longest common tactics that starts with tokens1[i] and tokens2[j]
        for (int i = 0; i < p1.size(); i++) {
            for (int j = 0; j < p2.size(); j++) {
                int curr1 = i;
                int curr2 = j;
                String start1 = p1.completeTokens.get(curr1).trim();
                String start2 = p2.completeTokens.get(curr2).trim();

                if (!validCustomTacticStart(start1) || !validCustomTacticStart(start2)) continue;
                Map<String, String> uniMap1To2 = new HashMap<>();
                while (curr1 < p1.size() && curr2 < p2.size()) {
                    // stop if generic sig doesn't match
                    if (!p1.cleanTokens.get(curr1).equals(p2.cleanTokens.get(curr2))) break;

                    // stop if syntax doesn't match
                    if (!ifSyntaxMatch(p1.completeTokens.subList(i, curr1 + 1),
                            p2.completeTokens.subList(j, curr2 + 1))) break;
                    List<String> t1Args = p1.args.get(curr1);
                    List<String> t2Args = p2.args.get(curr2);
                    // stop if arguments mapping doesn't work
                    boolean badMatch = false;
                    for (int k = 0; k < t1Args.size(); k++) {
                        if (uniMap1To2.containsKey(t1Args.get(k))) {
                            if (!uniMap1To2.get(t1Args.get(k)).equals(t2Args.get(k))) {
                                badMatch = true;
                                break;
                            } // if unification is consistent, just keep going
                        } else {
                            // if new arg is found
                            uniMap1To2.put(t1Args.get(k), t2Args.get(k));
                        }
                    }
                    if (badMatch) break;
                    curr1++;
                    curr2++;
                }

                // if gets here, compare with longest tactics
                if (curr1 - i > bestSize) {
                    bestStart = i;
                    bestSize = curr1 - i;
                }
            }
        }

        if (bestSize > 1) {
            BaselineProof tac = p1.getSubproof(bestStart, bestSize);
            tac.args = generateGenericArgs(p1.args, bestStart, bestStart + bestSize);
            return tac;
        }
        return null;
    }

    public static boolean canUnify(List<List<String>> args1, List<List<String>> args2) {
        Map<String, String> uniMap1To2 = new HashMap<>();
        for (int i = 0; i < args1.size(); i++) {
            List<String> t1Args = args1.get(i);
            List<String> t2Args = args2.get(i);
            for (int k = 0; k < t1Args.size(); k++) {
                if (uniMap1To2.containsKey(t1Args.get(k))) {
                    if (!uniMap1To2.get(t1Args.get(k)).equals(t2Args.get(k))) {
                        return false;
                    } // if unification is consistent, just keep going
                } else {
                    // if new arg is found
                    uniMap1To2.put(t1Args.get(k), t2Args.get(k));
                }
            }
        }
        return true;
    }

    public static boolean ifSyntaxMatch(List<String> p1, List<String> p2) {
        String s1 = String.join("", p1);
        String s2 = String.join("", p1);

        return formatValidTacticString(s1).equals(formatValidTacticString(s2));
    }

    public static boolean ifCompleteTactic(List<String> completeTokens) {
        int numLeftParen = 0;
        for (int i = 1; i < completeTokens.size(); i++) {
            for (char c : completeTokens.get(i).toCharArray()) {
                if (c == '[') numLeftParen++;
                if (c == ']') numLeftParen--;
            }
        }
        return (numLeftParen <= 0);
    }

    private static String formatValidTacticString(String s) {
        if (s.substring(0, 3).equals("; [")) {
            s = s.substring(3);
        }

        int numBracket = 0;
        int stopIndex = s.length();
        // make sure the bracket number matches
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '[') numBracket++;
            else if (c == ']') {
                numBracket--;
                if (numBracket > 0) continue;
                stopIndex = i + 1;
                break;
            }
        }
        if (numBracket == 0) return s.substring(0, stopIndex);
        if (s.charAt(s.length() - 1) == '|') s = s.substring(0, s.length() - 1);

        while (numBracket > 0) {
            s = s + ']';
            numBracket--;
        }

        return s;
    }

    public static List<List<String>> generateGenericArgs(List<List<String>> args, int start, int end) {
        int argID = 0;
        Map<String, String> argsToGenericArgs = new HashMap<>();
        List<List<String>> res = new ArrayList<>();
        while (start < end) {
            for (String arg: args.get(start)) {
                if (!argsToGenericArgs.containsKey(arg)) {
                    argsToGenericArgs.put(arg, "H" + (argID++));
                }
            }
            res.add(args.get(start).stream().map(a -> argsToGenericArgs.get(a)).collect(Collectors.toList()));
            start++;
        }
        return res;
    }

    public static boolean validCustomTacticStart(String start) {
        char startLast = start.charAt(start.length() - 1);
        if (startLast == '|') return false;
        if (start.substring(0, 3).equals("; [")) {
            int numBrancket = 0;
            for (char c: start.toCharArray()) {
                if (c == '[') numBrancket++;
                else if (c == ']') numBrancket--;
            }
            return numBrancket > 0;
        } else {
            return true;
        }
    }

    public static String getGenericSigProof(List<String> tokens, CoqProof coqProof, List<String> genericProofTokens, List<String> genericCompleteTokens, List<List<String>> args) {
        // format each token: remove the leading or trailing “;”, “.“, “|”, “[”, “]”
        String regex = "^[;\\.\\|\\[\\]]+|[;\\.\\[\\]]+$";
        List<String> cleanTokens = new ArrayList<>();

        for (int i = 0; i < tokens.size(); i++) {
            String token = tokens.get(i);
            int previousLength;
            do {
                previousLength = token.length();
                token = token.replaceAll(regex, "").trim();
            } while (token.length() < previousLength);
            int numRightBracket = 0;
            for (char c: token.toCharArray()) {
                if (c == '[') numRightBracket++;
                else if (c == ']') numRightBracket--;
            }
            for (int j = 0; j < numRightBracket; j++) {
                token += ']';
            }
            cleanTokens.add(processBrackets(token));
        }

        // in the corresponding proofs list, if the p.tactic.toCoqScript == token, get the signature and the corresponding args
        getGenericSigTokensRaw(cleanTokens, coqProof.tactics, genericProofTokens, args);
        getGenericCompleteTokens(tokens, cleanTokens, genericProofTokens, genericCompleteTokens);

        return "";
    }

    public static void getGenericCompleteTokens(List<String> tokens, List<String> cleanTokens, List<String> genericProofTokens, List<String> genericCompleteTokens) {
        // get a copy of the generic signature, replace the original with the generic
        // make generic tokens complete by replacing the clean token within the complete tokens
        for (int i = 0; i < tokens.size(); i++) {
            genericCompleteTokens.add(tokens.get(i).replace(cleanTokens.get(i), genericProofTokens.get(i)));
        }
    }

    public static String processBrackets(String s) {
        while (s.contains("[ ") || s.contains(" ]") || s.contains("( ") || s.contains(" )")) {
            s = s.replaceAll(" ]", "]");
            s = s.replaceAll(" \\)", ")");
            s = s.replaceAll("\\[ ", "[");
            s = s.replaceAll("\\( ", "(");
        }
        s = s.replaceAll("\\(", "( ");
        s = s.replaceAll("\\[", "[ ");
        s = s.replaceAll(" ; ", "; ").replaceAll(" : ", ": ");
        return s;
    }

    public static void getGenericSigTokensRaw(List<String> tokens, List<CoqTactic> tactics, List<String> genericProofTokens, List<List<String>> args) {
        Map<String, CoqTactic> signatureMap = new HashMap<>();
        for (CoqTactic t: tactics) {
            String s = t.toCoqScriptNoArgs();
            s = processBrackets(s);
            signatureMap.put(s.replace("_global_", ""), t);
        }
        for (int i = 0; i < tokens.size(); i++) {
            if (signatureMap.containsKey(tokens.get(i))) {
                CoqTactic coqTac = signatureMap.get(tokens.get(i));
                genericProofTokens.add(processBrackets(coqTac.signature.substring(0, coqTac.signature.length() - 2)));

                // get args
                String sigCopy = new String(coqTac.signature);
                List<String> inputArgs = coqTac.inputs.stream().filter(a -> !a.type.equals(CoqTactic.PROP_TYPE.GOAL)).map(a -> a.simpleName()).collect(Collectors.toList());
                List<String> outputArgs = coqTac.outputs.stream().filter(a -> !a.type.equals(CoqTactic.PROP_TYPE.GOAL)).map(a -> a.simpleName()).collect(Collectors.toList());
                int iInd = 0;
                int oInd = 0;
                List<String> argList = new ArrayList<>();
                while (sigCopy.contains(" _i") || sigCopy.contains(" _o")) {
                    int indexInput = sigCopy.contains(" _i") ? sigCopy.indexOf(" _i") : Integer.MAX_VALUE;
                    int indexOutput = sigCopy.contains(" _o") ? sigCopy.indexOf(" _o") : Integer.MAX_VALUE;

                    if (indexInput < indexOutput) {
                        sigCopy = sigCopy.replaceFirst(" _i", " ");
                        argList.add(iInd < inputArgs.size() ? inputArgs.get(iInd++) : argList.get(argList.size() - 1));
                        String a = argList.get(argList.size() - 1);
                        a = a.replace("_global_", "");
                        // Compile the pattern
                        Pattern pattern = Pattern.compile("^c\\d+_[a-zA-Z]+");

                        // Create a matcher to check if the input matches the regex
                        Matcher matcher = pattern.matcher(a);

                        // If the string matches the regex, replace the string
                        if (matcher.matches()) {
                            a = a.split("_", 2)[1];
                        }
                        argList.set(argList.size() - 1, a);
                    } else {
                        sigCopy = sigCopy.replaceFirst(" _o", " ");
                        argList.add(oInd < outputArgs.size() ? outputArgs.get(oInd++) : argList.get(argList.size() - 1));
                        argList.set(argList.size() - 1, argList.get(argList.size() - 1).replace("_global_", ""));
                    }
                }
                args.add(argList);
            } else {
                genericProofTokens.add(tokens.get(i));
                args.add(new ArrayList<>());
            }
        }
    }

    public static List<String> retrieveProofStringsFromFile(String filename) throws IOException {
        String content = new String(Files.readAllBytes(Paths.get(filename)));
        Pattern pattern = Pattern.compile("(Proof\\..*?(Qed|Defined)\\.|Next Obligation\\..*?Qed\\.)", Pattern.DOTALL);
        Matcher matcher = pattern.matcher(content);

        List<String> proofs = new ArrayList<>();

        while (matcher.find()) {
            proofs.add(matcher.group().replace("Proof.", "")
                    .replace("Next Obligation.", "").replace("Qed.", "")
                            .replace("Defined.", ""));
        }
        return proofs.stream()
                .filter(p -> !p.equals(" decide equality. ") && !p.equals(" apply (Genv.senv_match TRANSF). ")).toList(); // for Allocation
    }

    public static List<String> retrieveProofsForRefactoring(String content) throws IOException {
        Pattern pattern = Pattern.compile("((Proof|Next Obligation)\\..*?(Qed|Defined)\\.)", Pattern.DOTALL);
        Matcher matcher = pattern.matcher(content);

        List<String> proofs = new ArrayList<>();

        while (matcher.find()) {
            proofs.add(matcher.group().replaceAll("[\\s]{1,}", " "));
        }
        return proofs.stream().filter(p -> !p.equals("Proof. decide equality. Defined.") && // for Allocation
            !p.equals("Proof. apply (Genv.senv_match TRANSF). Qed.")).toList(); // LiveRange
    }

    public static List<String> tokenizeProof(String proof) {
        String ignore = ";;";
        proof = proof.replace(ignore, "!!");
        List<String> tokens = Arrays.stream(proof.split(";")).map(t -> t.trim()).collect(Collectors.toList());
        for (int i = 1; i < tokens.size(); i++) {
            tokens.set(i, "; " + tokens.get(i));
        }

        List<String> finalTokens = new ArrayList<>();
        for (String t: tokens) {
            // for each token, if it has (... | ...), replace the "|" with "!"
            // Define the regex pattern to match "(<random characters>|<random characters>)"
            String regex = "\\(([^)]+)\\)";
            Pattern pattern = Pattern.compile(regex);
            Matcher matcher = pattern.matcher(t);

            StringBuffer tokenSB = new StringBuffer();
            // Replace all occurrences of "|" with "!" if match the pattern (... | ...)
            while (matcher.find()) {
                String content = matcher.group(1); // Get the content within the parentheses
                if (content == null) continue;
                String replacedContent = content.replace("|", "*!*"); // Replace all "|" with "!"
                String replacement = "(" + replacedContent + ")"; // Reconstruct the replacement string
                matcher.appendReplacement(tokenSB, replacement); // Append the replacement to the result
            }
            matcher.appendTail(tokenSB);

            // break the token with "|"
            String token = tokenSB.toString();
            String pat = "intros( )+([A-Za-z_]+( )+)*\\[(.)*\\|(.)*\\](( )+[A-Za-z_])*|destruct()+(.)+()+as( )+\\[(.)*\\|(.)*\\]";
            Pattern compiledPattern = Pattern.compile(pat);
            matcher = compiledPattern.matcher(token);

            while (matcher.find()) {
                String matchedPart = matcher.group();
                String replace = matchedPart.replace("|", "*!*");

                token = token.replace(matchedPart, replace);
                matcher = compiledPattern.matcher(token);
            }

            if (token.contains("|")) {
                List<String> barSplits = Arrays.stream(token.split("\\|")).map(s -> s.trim()).collect(Collectors.toList());
                for (int i = 0; i < barSplits.size() - 1; i++) {
                    barSplits.set(i, barSplits.get(i) + " |");
                }
                finalTokens.addAll(barSplits);
            } else {
                finalTokens.add(token);
            }
        }

        // change "!" back to "|"
        tokens = finalTokens.stream().map(s -> s.replace("*!*", "|").replace("!!", ";;")).collect(Collectors.toList());

        return tokens;
    }

    public static List<String> tokenizeRawProof(String proof) {
        String ignore = ";;";
        proof = proof.trim().substring(0, proof.trim().length() - 1);
        proof = proof.replace(ignore, "!!");
        proof = proof.replace(".\n", ";");
        proof = proof.replace(". ", "; ");

        Pattern patternP = Pattern.compile("\\(([^()]*?);([^()]*?)\\)");
        Matcher matcherP = patternP.matcher(proof);

        // Replace ";" within the matched patterns with "*^*"
        proof = matcherP.replaceAll(m -> m.group().replace(";", "*^*"));

        List<String> tokens = Arrays.stream(proof.split(";")).map(t -> t.trim()).collect(Collectors.toList());
        String[] branchNotations = new String[] {"- ", "-- ", "--- ", "---- ",
                                                 "+ ", "++ ", "+++ ", "++++ ",
                                                 "* ", "** ", "***", "****"};
        for (int i = 1; i < tokens.size(); i++) {
            String s = tokens.get(i);
            if (s.charAt(s.length() - 1) == '.') {
                s = s.substring(0, s.length() - 1);
            }

            for (String n: branchNotations) {
                String pat = Pattern.quote(n);
                while (s.startsWith(n)) {
                    s = s.replaceFirst(Pattern.quote(n), " ");
                }
            }
            tokens.set(i, s.trim());
        }

        List<String> finalTokens = new ArrayList<>();
        for (String t: tokens) {
            // for each token, if it has (... | ...), replace the "|" with "!"
            // Define the regex pattern to match "(<random characters>|<random characters>)"
            String regex = "\\(([^)]+)\\)";
            Pattern pattern = Pattern.compile(regex);
            Matcher matcher = pattern.matcher(t);

            StringBuffer tokenSB = new StringBuffer();
            // Replace all occurrences of "|" with "!" if match the pattern (... | ...)
            while (matcher.find()) {
                String content = matcher.group(1); // Get the content within the parentheses
                if (content == null) continue;
                String replacedContent = content.replace("|", "*!*"); // Replace all "|" with "!"
                String replacement = "(" + replacedContent + ")"; // Reconstruct the replacement string
                if (replacement.contains(" /\\ ")) {
                    replacement = replacement.replaceAll(" /\\\\ ", " /\\\\\\\\ ");
                }
                if (replacement.contains(" \\/ ")) {
                    replacement = replacement.replaceAll(" \\\\/ ", " \\\\\\\\/ ");
                }
                matcher.appendReplacement(tokenSB, replacement); // Append the replacement to the result
            }
            matcher.appendTail(tokenSB);

            // break the token with "|"
            String token = tokenSB.toString();
            String pat = "intros( )+([A-Za-z_]+( )+)*\\[(.)*\\|(.)*\\](( )+[A-Za-z_])*|destruct()+(.)+()+as( )+\\[(.)*\\|(.)*\\]";
            Pattern compiledPattern = Pattern.compile(pat);
            matcher = compiledPattern.matcher(token);

            while (matcher.find()) {
                String matchedPart = matcher.group();
                String replace = matchedPart.replace("|", "*!*");

                token = token.replace(matchedPart, replace);
                matcher = compiledPattern.matcher(token);
            }

            finalTokens.add(token);
        }

        // change "!" back to "|"
        tokens = finalTokens.stream()
                .map(s -> s.replace("*!*", "|").replace("!!", ";;"))
                .map(s -> s.replace("*^*", ";"))
                .map(s -> processBrackets(s))
                .map(s -> s.replaceAll("\\{ ", "")
                        .replaceAll("} ", "")
                        .replaceAll("//\\\\ ", "//\\\\\\\\ ")
                        .replaceAll(" \\\\//", " \\\\\\\\//"))
                .collect(Collectors.toList());

        return tokens;
    }

}
