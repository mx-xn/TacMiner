package main.encode;

import main.enumeration.Abstraction;
import main.proofgraph.*;

import java.util.*;

/*
 * A representation of tactic sequences (a list of tactics labeled with a name).
 * On an abstract level, these may be used to represent PROOFS or LTACS (custom tactics)
 */
public class CoqProof {

    public enum SequenceType {
        PROOF,
        LTAC
    }

    public SequenceType type;
    public String lemma_name;

    public List<CoqTactic> tactics; // tactic list representation
    public ProofGraph pgraph; // proof graph representation

    public String raw_string; // optional string to store raw text
    public Map<Integer, List<Integer>> matches = new HashMap<>();

    public CoqProof(String lemma_name, List<CoqTactic> tactics, String raw_string, SequenceType type) {
        this.lemma_name = lemma_name;
        this.tactics = tactics;
        this.raw_string = raw_string;
        this.type = type;
        this.pgraph = null; // Don't instantiate until we need it
    }

    public CoqProof(String lemma_name, List<CoqTactic> tactics, String raw_string) {
        this(lemma_name, tactics, raw_string, SequenceType.PROOF);
    }
    
    public CoqProof(String lemma_name, List<CoqTactic> tactics) {
        this(lemma_name, tactics, null);
    }
    
    public CoqProof(CoqProof o) {
        this.lemma_name = o.lemma_name;
        this.tactics = new ArrayList<>(o.tactics);
        this.raw_string = o.raw_string;
        this.type = o.type;
        this.matches = o.matches;
        if (o.pgraph != null) {
            initProofGraph(); // Needs to be deep-copied
        }
    }

    public void initProofGraph() {
        if (this.pgraph == null)
            this.pgraph = new ProofGraph(this.tactics);
    }

    @Override
    public boolean equals(Object o){
        if(! (o instanceof CoqProof)) return false;

        CoqProof proof = (CoqProof) o;
        return this.lemma_name.equals(proof.lemma_name) & this.tactics.equals(proof.tactics) & this.type.equals(proof.type);
    }

    @Override
    public int hashCode(){
        return lemma_name.hashCode() + tactics.hashCode() + type.hashCode();
    }

    public String getRawString() {
        return raw_string;
    }

    public String condensedToString() {
        String type = (this.type == SequenceType.PROOF) ? "Lemma" : "Ltac";
        String ret = type + " " + lemma_name.toString() + ":\n";
        for (CoqTactic each: this.tactics) {
            ret += each.condensedToString() + " ";
        }
        return ret;
    }

    @Override
    public String toString() {
        String type = (this.type == SequenceType.PROOF) ? "Lemma" : "Ltac";
        return type + " " + lemma_name.toString() + ":\n" + tactics.toString();
    }

    public Map<String, Integer> getSigCount() {
        HashMap<String, Integer> count = new HashMap<>();
        for (CoqTactic t: this.tactics) {
            count.put(t.sig_no_out_arg, count.getOrDefault(t.sig_no_out_arg, 0) + 1);
        }
        return count;
    }
}