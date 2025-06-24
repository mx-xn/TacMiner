package trash.main;

import main.Main.*;
import main.config.*;
import main.encode.*;
import main.eval.*;
import main.lib_assembler.LibAssembler;
import main.proofgraph.*;
import trash.Engine;
import trash.sampler.*;

import java.io.IOException;
import java.util.*;
import org.junit.Test;

import static main.eval.CompressionEval.formatProof;
import static org.junit.jupiter.api.Assertions.*;

public class FormattingTest {
    
    public static void main (String[] args) {
        String tacs = "assert ( L : h l = Some v ) by ( rewrite Ph ; apply hupdate_same ); [destruct n as [  | ]; [constructor | custom0 hf hj h0 H H0 H1 hf hj h0 c' h' H H0 H1 H2; [subst h0; [custom14 l0 H; [congruence | .. ] | .. ] | subst h0; [custom18 ST ST; [cbn in H2; [rewrite L in H2; [congruence] | .. ] | .. ] | .. ] | inv H2; [assert ( v0 = v ); [congruence | subst v0; [cbn in H3; [rewrite L in H3; [custom5 h hj; [apply safe_pure; [split; [auto | auto | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ] | .. ].";

        System.out.println(tacs);
        System.out.println(CompressionEval.formatProof(tacs, 1));
    }

    @Test
    public void testFormatting() {
        String tacs = "unfold excluded_middle; [intros c3_H c3_P; [apply c3_H; [intros c5_H1 c5_H2; [contradiction | .. ] | .. ] | .. ] | .. ].";

        // assertEquals(CompressionEval.formatProof(tacs, 0), "");
    }
}
