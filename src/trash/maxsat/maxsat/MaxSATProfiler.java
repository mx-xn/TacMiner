package main.maxsat;

import java.io.*;

import static main.config.Path.maxsatFilesPath;

public class MaxSATProfiler {
    public static void maxSATVars() {
        String filePath = maxsatFilesPath + "sol.txt";  // Replace with the actual path to your file
        ProblemStatistics stats = readProblemStatistics(filePath);

        if (stats != null) {
            System.out.println("Number of variables: " + stats.getNumberOfVariables());
            System.out.println("Number of hard clauses: " + stats.getNumberOfHardClauses());
            System.out.println("Number of soft clauses: " + stats.getNumberOfSoftClauses());
        } else {
            System.out.println("Error reading problem statistics from file.");
        }
    }

    private static ProblemStatistics readProblemStatistics(String filePath) {
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            ProblemStatistics stats = new ProblemStatistics();

            String line;
            while ((line = reader.readLine()) != null) {
                if (line.contains("Number of variables:")) {
                    stats.setNumberOfVariables(Integer.parseInt(line.split("\\s+")[5]));
                } else if (line.contains("Number of hard clauses:")) {
                    stats.setNumberOfHardClauses(Integer.parseInt(line.split("\\s+")[6]));
                } else if (line.contains("Number of soft clauses:")) {
                    stats.setNumberOfSoftClauses(Integer.parseInt(line.split("\\s+")[6]));
                }
            }

            return stats;
        } catch (IOException | NumberFormatException e) {
            e.printStackTrace();
            return null;
        }
    }
}

class ProblemStatistics {
    private int numberOfVariables;
    private int numberOfHardClauses;
    private int numberOfSoftClauses;

    public int getNumberOfVariables() {
        return numberOfVariables;
    }

    public void setNumberOfVariables(int numberOfVariables) {
        this.numberOfVariables = numberOfVariables;
    }

    public int getNumberOfHardClauses() {
        return numberOfHardClauses;
    }

    public void setNumberOfHardClauses(int numberOfHardClauses) {
        this.numberOfHardClauses = numberOfHardClauses;
    }

    public int getNumberOfSoftClauses() {
        return numberOfSoftClauses;
    }

    public void setNumberOfSoftClauses(int numberOfSoftClauses) {
        this.numberOfSoftClauses = numberOfSoftClauses;
    }
}

