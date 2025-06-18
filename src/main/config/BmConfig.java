package main.config;

import org.checkerframework.checker.units.qual.A;

import java.util.*;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;

import static main.config.Paths.compressionEvalPath;

public class BmConfig {
    public static final int[] seeds = { 42, 1128, 2524, 68, 767 };
    public static final double fixedTestingPortion = 0.3;
    public static final int startPortion = 20;
    public static final int endPortion = 100;

    public int timeout;
    public String domain;
    public String topicPrefix;
    public String topic;
    public boolean visualizeGraphs = true;
    public Mode mode;
    public boolean training;
    public boolean random;
    public double stopThresh;

    public BmConfig(int timeout, String domain, String topicPrefix, String topic, Mode mode, boolean training,
                    boolean random, double stopThresh) {
        this.timeout = timeout;
        this.domain = domain;
        this.topicPrefix = topicPrefix;
        this.topic = topic;
        this.mode = mode;
        this.training = training;
        this.random = random;
        this.stopThresh = stopThresh;
    }

    public void updateStopThresh(int trainPortion) {
        this.stopThresh = (double) trainPortion / 100;
        this.training = true;
    }

    public BmConfig(String domain, String topicPrefix, String topic) {
        this.domain = domain;
        this.topicPrefix = topicPrefix;
        this.topic = topic;
    }

    public BmConfig(BmConfig c) {
        this.timeout = c.timeout;
        this.domain = c.domain;
        this.topicPrefix = c.topicPrefix;
        this.topic = c.topic;
        this.mode = c.mode;
        this.training = c.training;
        this.random = c.random;
        this.stopThresh = c.stopThresh;
    }

    public BmConfig() {
    }

    public enum Mode {
        ENUMERATION,
        ENUMERATION_SPLIT,
        BASELINE,
        PRUNING_ABL,
        GRAMMAR_ABL
    }

    public static final Map<Integer, Mode> modeMap = new HashMap<>() {{
        put(0, Mode.ENUMERATION);
        put(1, Mode.BASELINE);
        put(2, Mode.PRUNING_ABL);
        put(3, Mode.GRAMMAR_ABL);
        put(4, Mode.ENUMERATION_SPLIT);
    }};

    public static final BmConfig[] config = {
        // 7
        new BmConfig("cdf", ".", "Seplog"),
        new BmConfig("cdf", ".", "CSL"),
        new BmConfig("cdf", ".", "Hoare"),
        new BmConfig("cdf", ".", "Separation"),
        new BmConfig("cdf", ".", "Sequences"),

        new BmConfig("CompCert", "backend", "Allocation"),
        new BmConfig("CompCert", "backend", "Debugvarproof"),
        new BmConfig("CompCert", "backend", "NeedDomain"),
        new BmConfig("CompCert", "backend", "RTLgenspec"),
        new BmConfig("CompCert", "backend", "SplitLongproof_ref"),
        new BmConfig("CompCert", "common", "Events_ref"),
        new BmConfig("CompCert", "aarch64", "Conventions1_ref"),
        new BmConfig("CompCert", "lib", "Integers_ref"),

        new BmConfig("bignums", "BigN", "NMake"),
        new BmConfig("bignums", "BigQ", "QMake"),
        new BmConfig("bignums", "BigZ", "ZMake"),

        new BmConfig("coq-art", ".", "chap3"),
        new BmConfig("coq-art", ".", "chap5"),
        new BmConfig("coq-art", ".", "chap8"),
        new BmConfig("coq-art", ".", "chap6"),
        new BmConfig("coq-art", ".", "chap11"),
        new BmConfig("coq-art", ".", "chap15"),
        new BmConfig("coq-art", ".", "chap16"),
        new BmConfig("coq-art", ".", "impredicative"),
        new BmConfig("coq-art", ".", "parsing")
    };

    public static final Map<String, List<BmConfig>> BmConfigMap = new HashMap<String, List<BmConfig>>() {{
        put("cdf", Arrays.stream(config).toList().subList(0, 5));
        put("CompCert", Arrays.stream(config).toList().subList(5, 13));
        put("bignums", Arrays.stream(config).toList().subList(13, 16));
        put("coq-art", Arrays.stream(config).toList().subList(16, config.length));
    }};

    public String getJsonFilename() {
        return String.join("/", new String[] {this.domain, this.topicPrefix, "json", this.topic}) + ".json";
    }

    public String getInputFilename() {
        return String.join("/", new String[] {this.domain, this.topicPrefix, this.topic}) + ".v";
    }

    public static List<BmConfig> getBmConfig(int timeoutInSeconds, int mode, String domain, String topic,
                                                    int trainPortion, String random)  {
        List<BmConfig> res = new ArrayList<>();
        List<String> topics = topic.equals("all") ?
                BmConfigMap.get(domain).stream().map(c -> c.topic).toList() :
                Arrays.asList(topic);
        for (String t: topics) {
            BmConfig currConfig = null;
            for (BmConfig c: BmConfigMap.get(domain)) {
                if (c.topic.equals(t)) {
                    currConfig = new BmConfig(c);
                    break;
                }
            }

            if (res == null) {
                throw new NullPointerException("config is null. benchmark not found");
            }

            // set up other fields
            currConfig.timeout = timeoutInSeconds;
            currConfig.mode = modeMap.get(mode);
            currConfig.training = trainPortion < 100;
            if (trainPortion > 100) trainPortion = 100;
            currConfig.stopThresh = (double) trainPortion / 100;
            currConfig.random = random.equals("True");
            res.add(currConfig);
        }

        return res;
    }

//            new Config(1, 2, 600, "cdf/json/" + "Sequences.json", "cdf/Sequences.v", compressionEvalPath + "", true),
//            new Config(1, 2, 600, "cdf/json/" + "Separation.json", "cdf/Separation.v", compressionEvalPath + "", true),
//            new Config(1, 2, 1800, "cdf/json/" + "Seplog.json", "cdf/Seplog.v", compressionEvalPath + "", false),
//            new Config(1, 2, 1800, "cdf/json/" + "CSL.json", "cdf/CSL.v", compressionEvalPath + "", false),
//            new Config(1, 2, 600, "cdf/json/" + "Delay.json", "cdf/Delay.v", compressionEvalPath + "", false),
//            new Config(1, 2, 10, "cdf/json/" + "Monads.json", "cdf/Monads.v", compressionEvalPath + "", true),
//            new Config(1, 2, 600, "cdf/json/" + "Hoare.json", "cdf/Hoare.v", compressionEvalPath + "", true),
//
//            // 14
//            new Config(1, 2, 600, "atpl/json/" + "pi_calculus.json", "atpl/pi_calculus.v", compressionEvalPath + "", true),
//
//            // 15
//            new Config(1, 2, 600, "CompCert/backend/json/" + "Allocation.json", "CompCert/backend/Allocation.v", compressionEvalPath + "", true),
//            new Config(1, 2, 600, "CompCert/backend/json/" + "Debugvarproof.json", "CompCert/backend/Debugvarproof.v", compressionEvalPath + "", true),
//            new Config(1, 2, 600, "CompCert/backend/json/" + "NeedDomain.json", "CompCert/backend/NeedDomain.v", compressionEvalPath + "", true),
//            new Config(1, 2, 600, "CompCert/backend/json/" + "RTLgenspec.json", "CompCert/backend/RTLgenspec.v", compressionEvalPath + "", true)

//            new Config(1, 2, 500, "coq-art/json/" + "nth_length.json", "coq-art/nth_length.v", compressionEvalPath + "", false),
//            new Config(1, 2, 500, "coq-art/json/" + "exo_frac.json", "coq-art/exo_frac1.v", compressionEvalPath + "", true),
//            new Config(1, 2, 500, "coq-art/json/" + "chap3.json", "coq-art/chap3_raw.v", compressionEvalPath + "", true),
//            new Config(1, 2, 500, "coq-art/json/" + "chap5.json", "coq-art/chap5_raw.v", compressionEvalPath + "", true),
//            new Config(1, 2, 500, "coq-art/json/" + "chap8.json", "coq-art/chap8_raw.v", compressionEvalPath + "", true),
//            new Config(1, 2, 500, "coq-art/json/" + "class.json", "coq-art/class.v", compressionEvalPath + "", true),
//            new Config(1, 2, 500, "coq-art/json/" + "cut_example.json", "coq-art/cut_example.v", compressionEvalPath + "", true),

//        new Config(1, 2, 500, "coq-art/json/" + "parsing.json", "coq-art/parsing.v", compressionEvalPath + ""),
//        new Config(1, 2, 500, "coq-art/json/" + "chap9.json", "coq-art/chap9.v", compressionEvalPath + ""),
//
//        new Config(-1, 300, coqFilesPath + "SimpleProofs.json", coqFilesPath + "SimpleProofs.v", compressionEvalPath + "SimpleProofs_compressed.v"),
//        new Config(2, 600, coqFilesPath + "IntvSets.json", compCertPath + "lib/IntvSets.v", compressionEvalPath + "IntvSets_compressed.v"),
//        new Config(1, 2, 600, coqFilesPath + "Functor.json", categoryPath + "Theory/Functor_new.v", compressionEvalPath + "Functor_compressed.v"),
//        new Config(1, 2, 600, coqFilesPath + "LiveLockServ.json", categoryPath + "lib/LiveLockServ_new.v", compressionEvalPath + "LiveLockServ_compressed.v"),
//        new Config(1, 2, 1200, coqFilesPath + "Floats.json", categoryPath + "lib/Floats_new.v", compressionEvalPath + "Floats_compressed.v"),
//        new Config(1, 2, 1200, coqFilesPath + "SplitLongproof.json", categoryPath + "backend/SplitLongproof_new.v", compressionEvalPath + "SplitLongproof_compressed.v"),
//        new Config(1, 2, 300, coqFilesPath + "SelectOpproof.json", categoryPath + "arm/SelectOpproof_new.v", compressionEvalPath + "SelectOpproof_compressed.v"),
//        new Config(1, 2, 1500, coqFilesPath + "ParE.json", categoryPath + "Instance/Coq/ParE_new.v", compressionEvalPath + "ParE_compressed.v"),
//        new Config(7, 2, 30, coqFilesPath + "IntvSets.json", compCertPath + "lib/IntvSets.v", compressionEvalPath + "IntvSets_compressed.v"),
//        new Config(40, 2, 90, coqFilesPath + "IntvSets.json", compCertPath + "lib/IntvSets.v", compressionEvalPath + "IntvSets_compressed.v"),
//        new Config(1, 2, 90, coqFilesPath + "SimpleAlgebra.json", coqFilesPath + "SimpleAlgebra.v", compressionEvalPath + "SimpleAlgebra_compressed.v"),
//        new Config(4, 2, 90, coqFilesPath + "SimpleAlgebra2.json", coqFilesPath + "SimpleAlgebra2.v", compressionEvalPath + "SimpleAlgebra2_compressed.v")

}
