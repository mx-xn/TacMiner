package main;

import main.config.Path;
import main.encode.CoqProof;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

import static main.maxsat.MaxSATUtil.writeTo;

public class RegressionTest {
    public static void writeCustomTactics(String filename, Map<List<Integer>, List<CoqProof>> customTactics) throws IOException {
        StringBuilder content = new StringBuilder();
        for (Map.Entry<List<Integer>, List<CoqProof>> entry: customTactics.entrySet()) {
            List<String> tacStrings = entry.getValue().stream().map(tac -> tac.toString()).collect(Collectors.toList());
            content.append(entry.getKey().toString())
                    .append("\n")
                    .append(String.join("\n\n", tacStrings))
                    .append("\n");
        }
        System.out.println("writing \n" + content.toString() + "------");
        writeTo(content.toString(), Path.regressionPath + filename);
    }
}
