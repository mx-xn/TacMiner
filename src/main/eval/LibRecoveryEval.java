package main.eval;

import main.config.Path;

import java.io.*;
import java.util.*;

import static main.decode.utils.writeTo;

public class LibRecoveryEval {
    private class LibBenchmark {
        String signature;
        List<String> args;
        String body;
        String usageFilePath;
        String addBefore;

        private LibBenchmark(String sig, List<String> args, String bd, String path, String addBefore) {
            this.signature = sig;
            this.args = args;
            this.body = bd;
            this.usageFilePath = path;
            this.addBefore = addBefore;
        }
    }

    // Given a list of benchmark information, update the benchmarks in the corresponding files.
    // Save the modified files as new versions and return their filenames.
    public List<String> inlineBenchmarks(List<LibBenchmark> benchmarks) throws IOException {
        Map<String, List<LibBenchmark>> fileBenchmarksMap = groupBenchmarks(benchmarks);
        List<String> filenames = new ArrayList<>();
        for (String inputFile: fileBenchmarksMap.keySet()) {
            // get content of input file
            StringBuilder sb = new StringBuilder();
            try (BufferedReader br = new BufferedReader(new FileReader(inputFile))) {
                String line;
                while ((line = br.readLine()) != null) {
                    sb.append(line).append("\n");
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
            String content = sb.toString();

            // for each custom tactic to replace in the file, replace all usages of that tactic
            for (LibBenchmark benchmark: fileBenchmarksMap.get(inputFile)) {
                content = inlineTacticInString(new String(content), benchmark);
            }

            // writeNewFile
            String newFilename = inputFile.substring(0, inputFile.length() - 2) + "_new.v";
            filenames.add(newFilename);
            writeTo(content, newFilename);
        }

        return filenames;
    }

    private Map<String, List<LibBenchmark>> groupBenchmarks(List<LibBenchmark> benchmarks) {
        Map<String, List<LibBenchmark>> map = new HashMap<>();
        // group benchmarks based on the file they were used in
        for (LibBenchmark b: benchmarks) {
            if (!map.containsKey(b.usageFilePath))
                map.put(b.usageFilePath, new ArrayList<>());
            map.get(b.usageFilePath).add(b);
        }
        return map;
    }

    public String inlineTacticInString(String original, LibBenchmark benchmark) {
        StringBuilder sb = new StringBuilder();
        // replace args if needed
        while (original.indexOf(benchmark.signature) != -1) {
            String body = new String(benchmark.body);
            int indexStartReplace = original.indexOf(benchmark.signature);
            sb.append(original.substring(0, indexStartReplace));
            original = original.substring(indexStartReplace + benchmark.signature.length());

            Map<String, String> argReplaceMap = new HashMap<>();
            int cursorNext = benchmark.args.isEmpty() ? 0 : getArgReplaceMap(
                    original,
                    benchmark.args,
                    argReplaceMap);
            for (String argToReplace: argReplaceMap.keySet()) {
                body = body.replaceAll(argToReplace, argReplaceMap.get(argToReplace));
            }

            sb.append(body.substring(0, body.length() - 1));
            original = original.substring(cursorNext);
        }
        sb.append(original);

        return sb.toString();
    }

    // return end of replacement index
    private int getArgReplaceMap(String script, List<String> args, Map<String, String> argReplaceMap) {
        int numParentheses = 0;
        int cursor = 0;
        System.out.println("extracting args from scripts: " + script.substring(0, 30) + "...");
        for (String arg: args) {
            boolean found = false;
            StringBuilder argBuilder = new StringBuilder();
            while (!found) {
                System.out.println("current builder: " + argBuilder.toString());
                char c = script.charAt(cursor++);
                switch (c) {
                    case '(':
                        numParentheses++;
                        argBuilder.append(c);
                        break;
                    case ')':
                        numParentheses--;
                        argBuilder.append(c);
                        break;
                    case ' ':
                        if (numParentheses == 0 && !argBuilder.isEmpty()) {
                            System.out.println("found! replace " + arg + " with " + argBuilder.toString());
                            argReplaceMap.put(arg, argBuilder.toString());
                            found = true;
                        }
                        break;
                    case '.':
                        if (cursor < script.length() && script.charAt(cursor) != ' ' && script.charAt(cursor) != '\n') {
                            // if it's not an ending of the tactic
                            System.out.println("c is " + c + ", but is not tactic separator");
                            argBuilder.append(c);
                        } else {
                            argReplaceMap.put(arg, argBuilder.toString());
                            System.out.println("found! replace " + arg + " with " + argBuilder.toString());
                            found = true;
                        }
                        break;
                    case ';':
                        argReplaceMap.put(arg, argBuilder.toString());
                        System.out.println("found! replace " + arg + " with " + argBuilder.toString());
                        found = true;
                        break;
                    default:
                        System.out.println("appending " + c);
                        argBuilder.append(c);
                        break;
                }
            }
        }

        return cursor - 1;
    }


    // benchmark signature - body - usage-file-path
    private List<LibBenchmark> getBenchmarkInfo() {
        String filename = Path.libRecoveryPath + "benchmarks.txt";
        String benchmarkFile = "";

        try (BufferedReader br = new BufferedReader(new FileReader(filename))) {
            String line;
            while ((line = br.readLine()) != null) {
                if (line.trim().startsWith("//")) {
                    continue; // Skip this line
                }
                // Process the line
                benchmarkFile += line;
                benchmarkFile += "\n";
            }
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        List<LibBenchmark> benchmarkObjs = new ArrayList<>();
        String[] benchmarks = benchmarkFile.split("benchmark-separator!!!");
        for (String benchmark: benchmarks) {
            String[] fields = benchmark.trim().split("\n", 3);
            String body = fields[2].trim();
            String addBefore = "";

            // getting addBefore field (things to add before the usage of the tactic)
            if (body.indexOf("add-before-use:") != -1) {
                addBefore = body.split("add-before-use")[1].trim();
                body = body.split("add-before-use:")[0].trim();
            }

            // getting signature and args
            String[] tokens = body.substring(0, body.indexOf(":=")).trim().split(" ");
            String signature = tokens[1];
            List<String> args = new ArrayList<>();
            for (int i = 2; i < tokens.length; i++) {
                args.add(tokens[i]);
            }
            body = body.split(":=")[1].trim();
            benchmarkObjs.add(new LibBenchmark(signature, args, body, fields[1], addBefore));
        }
        return benchmarkObjs;
    }

    public List<String> getReplacedBenchmarkFiles() throws IOException {
        return inlineBenchmarks(getBenchmarkInfo());
    }
}
