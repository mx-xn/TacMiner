package trash.test.encode;

import main.encode.CoqTactic;
import org.junit.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

public class CoqTacticTest {

    @Test
    public void testTactic() {
        CoqTactic tac = new CoqTactic(  "induction _ .", "induction _ .",
                                        Arrays.asList("_goal : eq (Nat.add a O) a", "a : nat"),
                                        Arrays.asList("_goal : eq (Nat.add O O) O", "_goal : eq (Nat.add (S a) O) (S a)", "IHa : eq (Nat.add a O) a"));
        
        assertTrue(tac.inputs.get(0).type == CoqTactic.PROP_TYPE.GOAL);
        assertTrue(tac.inputs.get(1).type == CoqTactic.PROP_TYPE.HYP);
        assertTrue(tac.outputs.get(0).type == CoqTactic.PROP_TYPE.GOAL);
        assertTrue(tac.outputs.get(1).type == CoqTactic.PROP_TYPE.GOAL);
        assertTrue(tac.outputs.get(2).type == CoqTactic.PROP_TYPE.HYP);

        System.out.println(tac);
    }


}
