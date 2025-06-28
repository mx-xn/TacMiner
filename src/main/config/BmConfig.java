package main.config;
import java.util.*;

public class BmConfig {
    public static final int[] seeds = { 42, 1128, 2524, 68, 767 };
    public static final double fixedTestingPortion = 0.3;
    public static final int startPortion = 20;
    public static final int endPortion = 100;

    public int timeout;
    public String domain;
    public String topic;
    public boolean visualizeGraphs = true;
    public Mode mode;
    public boolean training;
    public double stopThresh;

    public BmConfig(int timeout, String domain, String topic, Mode mode, boolean training,
                    boolean random, double stopThresh) {
        this.timeout = timeout;
        this.domain = domain;
        this.topic = topic;
        this.mode = mode;
        this.training = training;
        this.stopThresh = stopThresh;
    }

    public void updateStopThresh(int trainPortion) {
        this.stopThresh = (double) trainPortion / 100;
        this.training = true;
    }

    public BmConfig(String domain, String topic) {
        this.domain = domain;
        this.topic = topic;
    }

    public BmConfig(BmConfig c) {
        this.timeout = c.timeout;
        this.domain = c.domain;
        this.topic = c.topic;
        this.mode = c.mode;
        this.training = c.training;
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
        new BmConfig("program-logics", "CSL"),
        new BmConfig("program-logics", "Hoare"),
        new BmConfig("program-logics", "Separation"),
        new BmConfig("program-logics", "Seplog"),

        new BmConfig("comp-cert", "RegAlloc"),
        new BmConfig("comp-cert", "LiveRange"),
        new BmConfig("comp-cert", "AbsDomain"),
        new BmConfig("comp-cert", "RTLSpec"),

        new BmConfig("bignums", "NMake"),
        new BmConfig("bignums", "QMake"),
        new BmConfig("bignums", "ZMake"),

        new BmConfig("coq-art", "IndPred"),
        new BmConfig("coq-art", "Reflection"),
        new BmConfig("coq-art", "SearchTree"),
    };

    public static final Map<String, List<BmConfig>> BmConfigMap = new HashMap<String, List<BmConfig>>() {{
        put("program-logics", Arrays.stream(config).toList().subList(0, 4));
        put("comp-cert", Arrays.stream(config).toList().subList(4, 8));
        put("bignums", Arrays.stream(config).toList().subList(8, 11));
        put("coq-art", Arrays.stream(config).toList().subList(11, config.length));
    }};

    public String getJsonFilename() {
        return String.join("/", new String[] {"benchmarks", this.domain, "json", this.topic}) + ".json";
    }

    public String getInputFilename() {
        return String.join("/", new String[] {"benchmarks", this.domain, "raw", this.topic}) + ".v";
    }

    public static List<BmConfig> getBmConfig(int timeoutInSeconds, int mode, String domain, String topic, int trainPortion)  {
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
            res.add(currConfig);
        }

        return res;
    }
}
