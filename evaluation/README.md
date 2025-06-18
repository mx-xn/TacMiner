# Evaluation with Copra

This contains code to run our evaluations using the Copra agents augmented with new tactics.

## Copra setup

First, checkout Copra:

```
[.../dream-prover/]$ git submodule init --recursive
```

Follow the setup instructions in Copra's README, but first read the notes below. Some specific observations not mentioned in their README:

* (Step 2) When setting up opam, in case you're in a machine where you can't install system packages, it's likely you won't have bubblewrap (a binary sandboxing wrapper that opam uses). In that case, you can set up opam manually (not using the script the Copra README refers to in step 2) using:

```
$ opam init --disable-sandboxing
```

* (Step 4) Use Python 3.10 when you setup your conda environment:

```
[.../dream-prover/copra]$ conda create -n dreamprover python==3.10
```

Some of the dependencies in Copra break with other Python versions. If `pip install -r requirements.txt` doesn't work, edit it to remove the version specification for numpy (i.e. just leave `numpy` in the line that contains it).

* (Step 5) Use the setup script provided in this directory:

```
[.../dream-prover/copra]$ ../evaluation/setup.sh
```

The original Copra setup script will also download and set up Lean and Isabelle, which we don't need for now. You can thus skip Step 6.

## Running a simple test

This runs a simple test using the few-shot Copra agent in Coq:

```
[copra]$ python src/main/eval_benchmark.py prompt_settings=coq_few_shot env_settings=bm25_retrieval eval_settings=n_4_few_gpt35 benchmark=simple_benchmark_1
```

## Using custom tactics with Copra

We need a few steps to let Copra agents (a) be able to use custom tactics, and (b) be aware that they are available.

First, to make it possible for the agent to use the custom tactics, the simplest way is to add the new tactics to the benchmark's Coq file, then recompile the relevant benchmark.
For example, suppose we're doing that for coq-art. The benchmark files should be here:

```
(dreamprover) poesia@cocoflops2:/scr/poesia/dream-prover/evaluation$ ls ../copra/data/benchmarks/coq-art
chap3.glob  chap3.vo    chap5.v   chap8.glob  class.glob  class.vo          cut_example.glob  cut_example.vo  exo_frac.v    Makefile.coq.conf  nth_length.v   proofs
chap3.v     chap5.glob  chap5.vo  chap8.v     class.v     CoqMakefile.conf  cut_example.v     exo_frac.glob   Makefile.coq  nth_length.glob    nth_length.vo  tactics
```

Note that here the benchmark has been compiled: we generated a Makefile with coq_makefile, and ran make to generate all the \*.vo files. 
Now, suppose we'll add the following custom tactics to this file. These were synthesized using dreamprover from the proofs from `chap3.v`:

```
custom0 H0 H1 H2 := intros H0 H1 H2; [apply H2; [assumption |apply H1; [assumption | .. ] | .. ] | .. ].
custom1 H0 H1 H2 := intros H0 H1 H2; [apply H1; [apply H2; [assumption | .. ] | .. ] | .. ].
custom2 H0 H1 := apply H0; [assumption |apply H1; [assumption | .. ] | .. ].
custom3 H0 := apply H0; [assumption | .. ].
```

## Adding tactics to the Coq proof script.

The first step is to then add these tactics to the file. It suffices to add them at the very beginning. We can later do this programatically, but for now let's just open the file and paste this at the beginning:

```coq
(** BEGIN_DREAMPROVER_TACTICS **)
Ltac custom0 H0 H1 H2 := intros H0 H1 H2; [apply H2; [assumption |apply H1; [assumption | .. ] | .. ] | .. ].
Ltac custom1 H0 H1 H2 := intros H0 H1 H2; [apply H1; [apply H2; [assumption | .. ] | .. ] | .. ].
Ltac custom2 H0 H1 := apply H0; [assumption |apply H1; [assumption | .. ] | .. ].
Ltac custom3 H0 := apply H0; [assumption | .. ].
(** END_DREAMPROVER_TACTICS **)

; (existing content)
Section Minimal_propositional_logic.
 Variables P Q R T : Prop.


 Theorem imp_trans : (P->Q)->(Q->R)->P->R.
 Proof.
; ...
```

After this, recompile the benchmark (e.g., by running make -f Makefile.coq).

Now, the custom tactics will be in scope in this file, so they should be enabled in interactive proofs. The next step is "indexing" each file. In the Copra proof state, we get the name of the theorem we're trying to prove. We'll use this to know which custom tactics to add to the prompt, so that the agent model knows it can use them.

## Indexing custom tactics in proof scripts

First, run the indexer:

```sh
(dreamprover) poesia@cocoflops2:/scr/poesia/dream-prover/copra$ python ../evaluation/index_tactics.py .
```

This should produce a file called tactic_index.json, which will have (1) the custom tactic headers in each of the files containing custom tactics, and (2) the theorem names in each of those files.

Now, we need to patch the Copra agent to include this header in the prompt when custom tactics are available.
Let's do it for the few-shot agent, implemented in src/baselines/gpt4/few_shot_policy.py

The diff copra.patch will modify Copra to do the following:

1- Load the index
2- Add parameters to the policy prompter so that we can inject the custom message showing the custom tactics
3- Look up the index when the policy is called to generate a proof for a theorem, and add the custom message when appropriate

To apply this patch, you can use `git apply`:

```sh
(dreamprover) poesia@cocoflops2:/scr/poesia/dream-prover/copra$ git apply ../evaluation/copra.patch
```
