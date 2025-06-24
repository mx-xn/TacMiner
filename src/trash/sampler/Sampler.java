package trash.sampler;

import main.encode.*;

import java.util.*;

/*
 * This class is for sampling proofs from the proof corpus to pass into the MaxSAT subroutine.
 * Sampled proofs should ideally exhibit similar tactic sequences.
 * Several sampling types are supported:
 *  - no sampling (i.e. all pairs of proofs)
 *  - cosine sampling (via cosine similarity, based on tactic signatures)
 *  - tbd
 */

public class Sampler {

    public enum SamplingType {
        NONE,
        COSINE
    }

    public static Map<CharSequence, Integer> proofToVec(CoqProof proof) {
        Map<CharSequence, Integer> map = new HashMap<>();
        for (CoqTactic tac : proof.tactics) {
            if (!map.containsKey(tac.signature)) {
                map.put(tac.signature, 0);
            }
            map.put(tac.signature, map.get(tac.signature) + 1);
        }
        return map;
    }

    public static double cosineSimilarity(CoqProof proof1, CoqProof proof2) {
        return new CosineSimilarity().cosineSimilarity(proofToVec(proof1), proofToVec(proof2));
    }

    public static List<List<CoqProof>> getSamples(List<CoqProof> proofs, SamplingType sampleType) {
        List<List<CoqProof>> samples = new ArrayList<>();
        switch (sampleType) {
            case NONE: {
                for (int i = 0; i < proofs.size(); i++) {
                    for (int j = i+1; j < proofs.size(); j++) {
                        samples.add(Arrays.asList(proofs.get(i), proofs.get(j)));
                    }
                }
                break;
            }
            case COSINE: {
                List<List<Integer>> pairs = new ArrayList<>();
                double[][] similarities = new double[proofs.size()][proofs.size()];
                for (int i = 0; i < proofs.size(); i++) {
                    for (int j = i+1; j < proofs.size(); j++) {
                        pairs.add(Arrays.asList(i, j));
                        similarities[i][j] = similarities[j][i] = Sampler.cosineSimilarity(proofs.get(i), proofs.get(j));
                    }
                }

                Collections.sort(pairs, (List<Integer> a, List<Integer> b) -> {
                    return Double.compare(similarities[b.get(0)][b.get(1)], similarities[a.get(0)][a.get(1)]);
                });

                for(List<Integer> pair : pairs) {
                    samples.add(Arrays.asList(proofs.get(pair.get(0)), proofs.get(pair.get(1))));
                }
                break;
            }
            default: {
                System.err.println("Sampling Type not yet supported");
            }
        }
        return samples;
    }

    public static List<List<CoqProof>> getSamples(List<CoqProof> proofs, SamplingType sampleType, int K) {
        List<List<CoqProof>> samples = getSamples(proofs, sampleType);
        return samples.subList(0, Math.min(K, samples.size()));
    }

}
