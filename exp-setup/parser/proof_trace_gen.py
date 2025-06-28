#!/usr/bin/env python3

import sys
import shutil
root_dir = f"{__file__.split('src')[0]}"
if root_dir not in sys.path:
    sys.path.append(root_dir)
import os
from typing import *
import json
import re

import utils
import coq_serapy
from coq_parser import CoqLineByLineReader
from coq_executor import CoqExecutor
from preprocess_semicolons import CoqSemicolonParser

class CoqCustomFileExec:
    global_marker = "_global_"

    def __init__(self, file_path: str = "src/resources/coq-conversion/SimpleAlgebra.v", out_file_path: str = "src/resources/coq-conversion/SimpleAlgebra.json", auto_sig_recorder: utils.AutoRecorder = None, project_root: str = None):
        os.chdir(root_dir)
        all_tactics = []
        with CoqSemicolonParser(file_path, auto_sig_recorder=auto_sig_recorder, project_root=project_root) as coq_exec:
            all_tactics = coq_exec.run_in_loop()

        self.coq_stdin_reader = CoqLineByLineReader(file_content="\n".join(all_tactics))
        self.coq_exec : CoqExecutor = CoqExecutor(
            use_human_readable_proof_context=True,
            proof_step_iter=self.coq_stdin_reader.instruction_step_generator(),
            project_root=project_root)
        self.out_file_path = out_file_path
        self.auto_sig_recorder = auto_sig_recorder
        self.auto_count = 0
        self.context_queue = [0]
        self.context_to_hyps = { 0 : [] }
        self.context_unique_id = 1

    def __enter__(self):
        self.coq_exec.__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.coq_exec.__exit__(exc_type, exc_value, traceback)

    symbols_regexp = (r',|(?::>)|(?::(?!=))|(?::=)|\)|\(|;|@\{|~|\+{1,2}|\*{1,2}'
                      r'|&&|\|\||(?<!\\)/(?!\\)|/\\|\\/|(?<![<*+-/|&])=(?!>)|%|'
                      r'(?<!<)-(?!>)|<-|->|<=|>=|<>|\^|\[|\]|(?<!\|)\}|\{(?!\|)')

    def get_words(self, string: str) -> List[str]:
        return [word for word in re.sub(
            r'((\.(\s|$))|' + self.symbols_regexp + ')',
            r' \1 ',
            string).split()
                if word.strip() != '']

    def build_outputs(self, cur_goal: int, raw_tactic: str, tactic: str, in_state: Dict[str, List[str]], out_state: Dict[str, List[str]], args: List[str], res: List[str]) -> str:
        words = self.get_words(tactic) # All tokens
        for idx, word in enumerate(words):
            if not idx == 0 and words[idx] in ['[', '('] and words[idx-1] == 'as':
                return None

        added_goals = len(out_state)
        out_str = "[  "
        for idx in range(added_goals):
            obligation = out_state[idx]
            for hyp in obligation["hypotheses"]:
                tokens = hyp.split(" : ", 1)
                all_defns = tokens[0].split(",")

                for defn in all_defns:
                    tac = defn + " : " + tokens[1]
                    if tac not in in_state["hypotheses"]:
                        out_str += "_o "

            out_str += "| "

        return out_str[:-2] + "]"

    def extract_tactic_sig(self, cur_goal: int, raw_tactic: str, tactic: str, in_state: Dict[str, List[str]], out_state: Dict[str, List[str]], args: List[str], res: List[str]) -> str:
        # Remove hypotheses
        words = self.get_words(tactic) # All tokens
        hyps = set(coq_serapy.get_vars_in_hyps(in_state["hypotheses"])) # Input hypotheses

        global_lemmas = set()
        for arg in args:
            if arg.startswith("_global_"):
                global_lemmas.add(arg[len(self.global_marker):arg.find(":")].strip())

        for idx,word in enumerate(words):
            if word in hyps:
                words[idx] = "_i"
            if word in global_lemmas:
                words[idx] = "_i" # Can also replace here, for example with _g

        # number of resulting hypotheses
        out_hyps = set()
        for h in res:
            if not "_goal" in h:
                out_hyps.add(h)

        hyps_simple = set()
        for h in out_hyps:
            hyps_simple.add(h.split(" ", 2)[0].split("_", 2)[1])

        sig_no_out_arg = ".".join(" ".join(words).split(" . "))
        # if words[0] == auto, get implicit argument

        # Process tactics that take special casework
        # TODO: need to deal with different tactic forms (especially those that specify an output, which should be ignored)
        # hyps = hyps.union(set(coq_serapy.get_vars_in_hyps(out_state["hypotheses"]))) # Output hypotheses

        # if words[0] == "induction": # Handle natural number arguments in induction
        #     arg = re.match(r'\d+', words[1])
        #     if not arg == None:
        #         words[1] = "_"
        if words[0] in ["assumption, eassumption, reflexivity, trivial, auto, eauto, tauto, intuition",
                        "discriminate", "exact", "contradiction", "constructor", "econstructor", "ring"
                                                                                                 "field", "omega", "lia", "congruence", "left", "right", "split", "exfalso", "clear"]:
            # Simple tactic, do nothing
            pass
        elif words[0] in ["simpl", "fold", "unfold", "apply", "eapply", "rewrite"]:
            # Tactics create 1 output, but they take the same name
            pass
        elif words[0] in ["intro", "eintro"] and len(words) <= 2:
            # intro with no outputs specified
            words = [words[0], "_o", "."]
        elif words[0] in ["intros", "eintros"] and len(words) <= 2:
            # intros with no outputs specified
            words = [words[0]] + ["_o"] * len(out_hyps) + ["."] # multiple outputs
        elif words[0] in ["intro", "eintro", "intros", "eintros"]:
            # intro(s) with outputs specified
            for idx,word in enumerate(words):
                if word in hyps_simple:
                    words[idx] = "_o"
        elif words[0] in ["destruct", "edestruct"]:
            is_inductive = False

            # if the output is specified as "eqn:H", then this is an inductive destruct
            for idx, word in enumerate(words):
                if not idx == 0 and words[idx] == ':' and words[idx-1] == 'eqn':
                    is_inductive = True
                    words[idx+1] = "_o"

            # if the output is not specified, try appending eqn:H
            if not is_inductive:
                named_tactic = raw_tactic + " eqn:unique_id_h_x8hkl32DDk"
                try:
                    # Try this new named tactic
                    self.coq_exec.coq.cancel_last()
                    self.coq_exec.coq.run_stmt(named_tactic, timeout=self.coq_exec.timeout_in_sec)
                    # Revert to old tactic
                    self.coq_exec.coq.cancel_last()
                    self.coq_exec.coq.run_stmt(raw_tactic, timeout=self.coq_exec.timeout_in_sec)

                    is_inductive = True
                    words = words[:-1] + ["eqn", ":", "_o", "."]
                except:
                    pass

            if not is_inductive:
                # Still not inductive: then must be a conjunction or disjunction. Build "as []" statement
                outbranch_vars = self.build_outputs(cur_goal, raw_tactic, tactic, in_state, out_state, args, res)
                if outbranch_vars is not None:
                    words = words[:-1] + ["as", outbranch_vars, "."]
        # elif words[0] == "induction":
        #     outbranch_vars = self.build_outputs(cur_goal, raw_tactic, tactic, in_state, out_state, args, res)
        #     if outbranch_vars is not None:
        #         words = words[:-1] + ["as", outbranch_vars, "."]
        if words[0] == "simple" and words[1] == "induction":
            if len(words) > 2:
                if not words[2].isdigit():
                    words = [words[0], words[1], "_o", "."]
        else:
            pass
            # print("Tactic " + tactic + " not yet supported")
        # subst, inversion, replace, cut, assert, exists, eexists, elim

        return (".".join(" ".join(words).split(" . ")), sig_no_out_arg)

    def parse_tactic(self, tactic: str, tactic_list: Dict[str, any]):

        # After preprocessing, tactics are guaranteed to operate on only one context
        cur_goal = 0
        true_context = 0
        stripped_tactic = tactic
        match = re.match(r'(\d+)\s*:\s*([\s\S]+)', tactic)
        if not match == None: # Remove goal label from tactic
            cur_goal = int(match.group(1))
            stripped_tactic = match.group(2)
            true_context = self.context_queue[cur_goal - 1]

        # Process input state
        in_state = { "goal_index" : cur_goal, "hypotheses": [], "goal": "" }
        num_goals_pre = 0

        if self.coq_exec.coq.proof_context:
            num_goals_pre = len(self.coq_exec.coq.proof_context.fg_goals)
            obligation = self.coq_exec.coq.proof_context.fg_goals[cur_goal - 1].to_dict()
            for hyp in obligation["hypotheses"]:
                tokens = hyp.split(" : ", 1)
                all_defns = tokens[0].split(",")
                for defn in all_defns:
                    tac = defn + " : " + tokens[1]
                    in_state["hypotheses"].append(tac)
            in_state["goal"] = obligation["goal"]

        # Run tactic
        self.coq_exec.coq.run_stmt(tactic, timeout=self.coq_exec.timeout_in_sec)

        # Parse output state
        out_state = []
        extra_goals = len(self.coq_exec.coq.proof_context.fg_goals) - num_goals_pre
        current_context_copy = []
        if len(self.context_to_hyps) > 1:
            current_context_copy = self.context_to_hyps[true_context].copy()
        self.context_queue = self.context_queue[:cur_goal-1] + self.context_queue[cur_goal:]
        tactic_res = []
        tactic_args = []
        for g in range(max(cur_goal, 1), cur_goal + extra_goals + 1):
            out_context = { "goal_index" : g, "hypotheses": [], "goal": [] }
            obligation = self.coq_exec.coq.proof_context.fg_goals[g - 1].to_dict()

            context_id = true_context
            if obligation["goal"] == in_state["goal"] and extra_goals == 0:
                self.context_queue = self.context_queue[:g-1] + [true_context] + self.context_queue[g-1:]
            else:
                self.context_queue = self.context_queue[:g-1] + [self.context_unique_id] + self.context_queue[g-1:]
                context_id = self.context_unique_id
                self.context_unique_id += 1
                tactic_res = tactic_res + ["c" + str(context_id) + "_goal : " + obligation["goal"]]

            if context_id not in self.context_to_hyps:
                self.context_to_hyps[context_id] = []
                hyp_dict = coq_serapy.get_indexed_vars_dict(in_state["hypotheses"])
                for idx, hyp in enumerate(current_context_copy):
                    hyp_name = hyp.split('_', 1)[1].strip()
                    if hyp_name in hyp_dict:
                        self.context_to_hyps[context_id].append(hyp)

            for hyp in obligation["hypotheses"]:
                tokens = hyp.split(" : ", 1)
                all_defns = tokens[0].split(",")

                for idx,defn in enumerate(reversed(all_defns)):
                    tac = defn + " : " + tokens[1]
                    out_context["hypotheses"].append(tac)

                    if not tac in in_state["hypotheses"]:
                        new_hyp = "c" + str(context_id) + "_"
                        self.context_to_hyps[context_id].append(new_hyp + defn)
                        tactic_res.append(new_hyp + tac)

            out_context["goal"] = obligation["goal"]
            out_state.append(out_context)

        # print(in_state)
        # print(out_state)
        # print(self.context_queue)
        # print(self.context_to_hyps)

        # For simplicity, we'll assume any branching tactic always depends on the goal
        # (This is not necessarily true, for example with assert, but these cases are a rarity)
        if not len(out_state) == 1 or not in_state["goal"] == out_state[0]["goal"]:
            tactic_args = ["c" + str(true_context) + "_goal : " + in_state["goal"]] + tactic_args

        # Extract hypotheses
        words = self.get_words(stripped_tactic)
        hyp_dict = coq_serapy.get_indexed_vars_dict(in_state["hypotheses"])
        for idx, word in enumerate(words):
            if word in hyp_dict:
                for idx, hyp in enumerate(reversed(self.context_to_hyps[true_context])):
                    hyp_name = hyp.split('_', 1)[1].strip()
                    if hyp_name == word:
                        for h in in_state["hypotheses"]:
                            if h.split(":", 1)[0].strip() == hyp_name:
                                tactic_args.append(hyp + " : " + h.split(":", 1)[1].strip())
                                break
                        break
            else:
                try:
                    global_lemma = coq_exec.coq_exec.coq.check_term(word).split(":", 1)
                    global_name = word
                    global_type = global_lemma[1].strip()

                    # Add additional restrictions here
                    if global_type == "nat" or global_type == "Z": # Example restriction: exclude numbers
                        continue
                    # if idx == 0 or (not words[0] == "apply" and not words[0] == "rewrite" and not words[0] == "unfold" and not words[0] == "eapply" and not words[0] == "eelim"): # Example restriction: only process terms following "apply" or "rewrite"
                    if idx == 0 or (not words[0] == "apply" and not words[0] == "rewrite" and not words[0] == "unfold" and not words[0] == "eapply"): # Example restriction: only process terms following "apply" or "rewrite"
                        continue
                    # if not words[idx-1] == "apply" and not words[idx-1] == "rewrite" and not words[idx-1] == "unfold" and not words[idx-1] == "eapply": # Example restriction: only process terms following "apply" or "rewrite"
                    #     continue

                    tactic_args.append(f"{self.global_marker}{global_name} : {global_type}")
                except:
                    pass
        # Retrieve tactic signature
        (tactic_sig, tactic_sig_no_outarg) = self.extract_tactic_sig(cur_goal, tactic, stripped_tactic, in_state, out_state, tactic_args, tactic_res)

        # if tactic is intros, flip the hyp args
        words = [s.strip() for s in tactic_sig.split(" ")]
        if words[0] == "intros" and not words[1] == "until":
            tactic_res[1:] = reversed(tactic_res[1:])

        len_orig = len(tactic_args)
        # Deal with search tactics: manually remove hypotheses and see if the tactic still goes through
        automated_solvers = ["auto", "eauto", "assumption", "eassumption", "HDISJ", "subst", "intuition", "destruct"]
        if len([value for value in words if value in automated_solvers]) > 0:
            self.coq_exec.coq.cancel_last()
            obligation = self.coq_exec.coq.proof_context.fg_goals[cur_goal - 1].to_dict()
            for hyp in obligation["hypotheses"]:
                tokens = hyp.split(" : ", 1)
                all_defns = tokens[0].split(",")
                for defn in all_defns:
                    clear_tac = str(cur_goal) + ": clear " + defn + "; "
                    worked = True
                    try:
                        ng = len(self.coq_exec.coq.proof_context.fg_goals)
                        self.coq_exec.coq.run_stmt(clear_tac + stripped_tactic, timeout=self.coq_exec.timeout_in_sec)
                        if len(self.coq_exec.coq.proof_context.fg_goals) >= ng and not words[0] == "subst":
                            worked = False
                        self.coq_exec.coq.cancel_last()
                    except Exception as e:
                        if words[0] == "subst":
                            if "Cannot find any non-recursive equality" in str(e):
                                worked = False
                        else:
                            if "is used in" not in str(e) or "is used in conclusion" in str(e):
                                worked = False

                    if not worked:
                        for idx, hyp in enumerate(reversed(current_context_copy)):
                            hyp_name = hyp.split('_', 1)[1].strip()
                            if hyp_name == defn:
                                if hyp + " : " + tokens[1] not in tactic_args:
                                    tactic_args.append(hyp + " : " + tokens[1])
                                break

            # Restore state
            self.coq_exec.coq.run_stmt(tactic, timeout=self.coq_exec.timeout_in_sec)

        # if special case, more processing with hyps
        words = self.get_words(stripped_tactic)
        # print("in extract_Args, tactic is: " + tactic_sig)
        # sig_words = self.get_words(tactic_sig)
        # if words[0] in ["generalize", "pattern"]:
        #     (end, hyp, hyp_sig) = utils.ParserAid.get_actual_and_sig_hyp(1, words, sig_words)
        #     (tactic_sig, tactic_sig_no_outarg, tactic_args) = utils.ParserAid.get_arg_replaced_sigs(1, hyp, hyp_sig, tactic_args, tactic_sig, tactic_sig_no_outarg, "_hyp")
        # elif words[0] in ["split"] and words[1] == "with":
        #     (end1, hyp1, hyp_sig1) = utils.ParserAid.get_actual_and_sig_hyp(2, words, sig_words)
        #     (end2, hyp2, hyp_sig2) = utils.ParserAid.get_actual_and_sig_hyp(end1, words, sig_words)

        #     (tactic_sig, tactic_sig_no_outarg, tactic_args) = utils.ParserAid.get_arg_replaced_sigs(1, hyp1, hyp_sig1, tactic_args, tactic_sig, tactic_sig_no_outarg, "_hyp_1")
        #     (tactic_sig, tactic_sig_no_outarg, tactic_args) = utils.ParserAid.get_arg_replaced_sigs(2, hyp2, hyp_sig2, tactic_args, tactic_sig, tactic_sig_no_outarg, "_hyp_2")

        # print("new sig:", tactic_sig)

        # Replace all existential holes
        for arg in tactic_args:
            for tac in tactic_list:
                for idx,past_arg in enumerate(tac["tactic_args"]):
                    diff = [i for i in range(min(len(arg), len(past_arg))) if arg[i] != past_arg[i]]
                    if len(diff) > 0 and past_arg[diff[0]] == '?':
                        tac["tactic_args"][idx] = arg
                for idx,past_arg in enumerate(tac["tactic_res"]):
                    diff = [i for i in range(min(len(arg), len(past_arg))) if arg[i] != past_arg[i]]
                    if len(diff) > 0 and past_arg[diff[0]] == '?':
                        tac["tactic_res"][idx] = arg

        if len_orig > 0 and (len(tactic_res) > 0 or "subst" not in tactic_sig):
            # Append tactic application (ignore useless tactics)
            tactic_list.append({ "tactic_sig": tactic_sig,
                                 "tactic_sig_no_out_arg": tactic_sig_no_outarg,
                                 "tactic_args": tactic_args,
                                 "tactic_res": tactic_res})

        print("Processed tactic: " + tactic)


    def run_in_loop(self):
        last_stmt = None
        curr_lemma = None
        proof_list = []
        tactic_list = []

        while True:
            try:
                cmd_ran = self.coq_exec.run_next()
                last_stmt = self.coq_exec.current_stmt

                if self.coq_exec.is_in_proof_mode(): # Skip things that aren't true tactics
                    if "".join(last_stmt.split()) in ["Proof.", "Qed.", "-", "+", "*", "--", "++", "**", "---", "+++", "***", "----", "++++", "****", "{", "}"]:
                        pass
                    else:
                        self.coq_exec.coq.cancel_last()
                        self.parse_tactic(last_stmt, tactic_list)
                        curr_lemma = self.coq_exec.get_current_lemma_name()
                elif not len(tactic_list) == 0:
                    # Proof completed
                    if len(tactic_list) > 2 and "Next Obligation" not in tactic_list[1]["tactic_sig"]:
                    # if "Next Obligation" not in tactic_list[1]["tactic_sig"]: #todo: change back during normal runs
                        proof_list.append({ "lemma_name": curr_lemma, "proof": tactic_list })
                    tactic_list = []
                    self.context_queue = [0]
                    self.context_unique_id = 1
                    self.context_to_hyps = { 0 : [] }

                if not cmd_ran:
                    break
                # print(f"Coq> {self.coq_exec.current_stmt}")
            except:
                raise
            pass

        # Final pass-through: replace custom notation
        def replace_custom_notation(input):
            return input.replace("/ /\\\\ \\\\", "//\\\\\\\\") \
                .replace("\\\\ \\\\/ /", "\\\\\\\\//") \
                .replace("- - *", "--*") \
                .replace("- -> >", "-->>") \
                .replace("= ?", "=?") \
                .replace(": :", "::")

        # Output JSON to file
        proof_list = json.dumps(proof_list, indent=4, cls=utils.SetEncoder)
        with open(self.out_file_path, "w") as outfile:
            outfile.write(replace_custom_notation(proof_list))

if __name__ == "__main__":
    files_to_process = {
        # topic-name: (original_dir, original_filename, bench_dir)
        # "chap3_TM": ("coq-art", "chap3_TM.v", "coq-art"),
        # "chap3_PN": ("coq-art", "chap3_PN.v", "coq-art"),

        "chap5_comp_TM": ("coq-art", "chap5_comp_TM.v", "coq-art"),
        # "chap5_comp_PN": ("coq-art", "chap5_comp_PN.v", "coq-art"),

        # "chap11_comp_TM": ("coq-art", "chap11_comp_TM.v", "coq-art"),
        # "chap11_comp_PN": ("coq-art", "chap11_comp_PN.v", "coq-art"),

        # "IndPred_TM": ("coq-art", "IndPred_TM.v", "coq-art"),
        # "IndPred_PN": ("coq-art", "IndPred_PN.v", "coq-art"),

        # "impredicative_TM": ("coq-art", "impredicative_comp_TM.v", "coq-art"),
        # "impredicative_PN": ("coq-art", "impredicative_comp_PN.v", "coq-art"),

        # "parsing_TM": ("coq-art", "parsing_TM.v", "coq-art"),
        # "parsing_PN": ("coq-art", "parsing_PN.v", "coq-art"),

        # "IndPred": ("coq-art", "chap8.v", "coq-art"),
        # "SearchTree": ("coq-art", "chap11.v", "coq-art"),
        # "Reflection": ("coq-art", "chap16.v", "coq-art")

        # "RegAlloc" : ("CompCert", "backend/Allocation.v", "comp-cert"),
        # "LiveRange" : ("CompCert", "backend/Debugvarproof.v", "comp-cert"),
        # "AbsDomain" : ("CompCert", "backend/NeedDomain.v", "comp-cert"),
        # "RTLSpec" : ("CompCert", "backend/RTLgenspec.v", "comp-cert")

        # "Hoare" : ("cdf", "Hoare.v", "program-logics"),
        # "Separation" : ("cdf", "Separation.v", "program-logics"),
        # "Seplog" : ("cdf", "Seplog.v", "program-logics"),
        # "CSL" : ("cdf", "CSL.v", "program-logics"),

        # "NMake" : ("bignums", "BigN/NMake.v", "bignums"),
        # "ZMake" : ("bignums", "BigZ/ZMake.v", "bignums"),
        # "QMake" : ("bignums", "BigQ/QMake.v", "bignums")
    }
    root_dir = os.getcwd() + "/../../"
    os.chdir(root_dir)

    for topic in files_to_process:
        (original_dir, original_fn, bench_dir) = files_to_process[topic]
        json_path = "benchmarks/%s/json/" % bench_dir
        if not os.path.exists(os.path.dirname(json_path)):
            os.makedirs(os.path.dirname(json_path))

        coq_file = "raw-data/%s/%s" % (original_dir, original_fn)
        # shutil.copy(coq_file, "benchmarks/%s/raw/%s.v" % (bench_dir, topic))
        with CoqCustomFileExec(coq_file, "%s/%s.json" % (json_path, topic), project_root="raw-data/%s/" % original_dir) as coq_exec:
            coq_exec.run_in_loop()
