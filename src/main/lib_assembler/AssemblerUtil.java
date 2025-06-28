package main.lib_assembler;

import main.encode.CoqProof;

import java.util.*;

import static main.eval.CompressionEval.compressLibTacs;


public class AssemblerUtil {
    static int numNodes = 0;  
    static Map<CoqProof, Integer> idAssigner = new HashMap<>(); 
    private static class TacNode {
        int id;
        CoqProof tactic;
        List<TacNode> children = new ArrayList<>();
        List<TacNode> parents = new ArrayList<>();
        double mcp;
        double cp;
        protected TacNode(CoqProof tactic) {
            this.id = numNodes;
            numNodes++;
            this.tactic = tactic;
            idAssigner.put(tactic, this.id);
        }

        protected void setCP(double cp) {
            this.cp = cp;
        }

        protected void setMCP(double mcp) {
            this.mcp = mcp;
        }

        protected double calculateCP(int corpusSize) {
            return (double)this.size() * (double)this.tactic.matches.size() / (double) corpusSize;
        }

        protected void addChildren(TacNode n) {
            this.children.add(n);
        }

        protected void addParent(TacNode n) {
            this.parents.add(n);
        }

        protected int size() {
            return this.tactic.tactics.size();
        }

        @Override
        public boolean equals(Object o){
            if(! (o instanceof TacNode)) return false;

            TacNode n = (TacNode) o;
            return this.tactic.equals(n.tactic);
        }
    }

    protected static List<TacNode> formForests(Set<CoqProof> candidates) {
        List<TacNode> res = new ArrayList<>();
        // map from each tactic to its node
        Map<CoqProof, TacNode> nodePointer = new HashMap<>();
        numNodes = 0;

        // sort by size
        List<CoqProof> sorted = candidates.stream().sorted((t1, t2) -> (t2.tactics.size() - t1.tactics.size())).toList();
        Set<CoqProof> added = new HashSet<>();
        for (CoqProof t: sorted) {
            // if t is not added, it is a root itself
            if (!added.contains(t)) {
                TacNode n = new TacNode(t);
                added.add(t);
                res.add(n);
                nodePointer.put(t, n);
            }

            // get the coresponding nodes, and add children to it
            TacNode tacNode = nodePointer.get(t);
            int currInd = sorted.indexOf(t);
            currInd++;

            while (currInd < sorted.size()) {
                // if size equals, skip
                if (sorted.get(currInd).tactics.size() >= tacNode.size()) {
                    currInd++;
                    continue;
                }

                // check if tacNode can be compressed with currTactic, if yes, add a pointer
                List<List<CoqProof>> childrenCandidates = compressLibTacs(sorted.get(currInd),
                        Arrays.asList(new CoqProof(t)));
                if (childrenCandidates.size() < 2) {
                    currInd++;
                    continue;
                }

                // t can be compressed with curr tactic, hence curr tactic is a child of tactic
                if (!added.contains(sorted.get(currInd))) {
                    TacNode childNode = new TacNode(sorted.get(currInd));
                    added.add(sorted.get(currInd));
                    nodePointer.put(sorted.get(currInd), childNode);
                }
                TacNode childNode = nodePointer.get(sorted.get(currInd));
                tacNode.addChildren(childNode);
                childNode.addParent(tacNode);

                // if currTactic is a child of a parent of t, then remove currTactic from p.children
                for (TacNode p: tacNode.parents) {
                    if (childNode.parents.contains(p)) {
                        p.children.remove(childNode);
                        childNode.parents.remove(p);
                    }
                }
                currInd++;
            }

            // when processing a vertex c, if c is a child of b, and c is also a child of a, then we remove the
            // connection (a -> c)
        }

        return res;
    }


    private static void assignCompressionAndBound(TacNode root, int corpusSize, Set<CoqProof> remove) {
        root.setCP(root.calculateCP(corpusSize));
        // go down the tree, assign CP until hit the bottom, then go back up and assign
        // the MCP
        if (root.children == null || root.children.isEmpty()) {
            // hit bottom, just assign mcp
            root.setMCP(root.cp);
        } else {
            double sumChildrenCP = 0;
            // can still go deeper, call current call again
            for (TacNode c: root.children) {
                assignCompressionAndBound(c, corpusSize, remove);
                sumChildrenCP += c.mcp;
            }
            // calculate sum of CP of children
            root.setMCP(sumChildrenCP > root.cp ? sumChildrenCP : root.cp);
            if (root.cp >= root.mcp) {
                remove.addAll(root.children.stream().map(c -> c.tactic).toList());
            }
        }
    }

    public static Set<CoqProof> removeLowCompressionTactics(Set<CoqProof> candidates, int corpusSize) {
        Set<CoqProof> res = new LinkedHashSet<>();

        // given the candidates, return a list of graphs of candidates
        List<TacNode> forests = formForests(candidates);
        System.out.println("forests formed");

        // for each graph, assign CP and MCP, meanwhile add to the removeList
        Set<CoqProof> remove = new HashSet<>();
        for (TacNode root: forests) {
            assignCompressionAndBound(root, corpusSize, remove);
        }

        // return the tactics based on their original order
        for (CoqProof c: candidates) {
            if (!remove.contains(c)) {
                res.add(c);
            }
        }
        return res;
    }

}
