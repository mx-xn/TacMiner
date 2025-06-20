#!/usr/bin/env python3

import sys
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

class CoqSemicolonParser:
    def __init__(self, file_path: str = "src/resources/coq-conversion/SimpleAlgebra.v", auto_sig_recorder: utils.AutoRecorder = None, project_root: str = None):
        self.coq_stdin_reader = CoqLineByLineReader(file_path)
        self.coq_exec : CoqExecutor = CoqExecutor(
            use_human_readable_proof_context=True,
            proof_step_iter=self.coq_stdin_reader.instruction_step_generator(),
            project_root=project_root)
        self.auto_sig_recorder = auto_sig_recorder
        self.auto_count = 0
        self.all_tactics = []

    def __enter__(self):
        self.coq_exec.__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.coq_exec.__exit__(exc_type, exc_value, traceback)

    def parse_tactic(self, tactic: str):
        # Run tactic
        goals_before = len(self.coq_exec.coq.proof_context.fg_goals + self.coq_exec.coq.proof_context.bg_goals)

        self.coq_exec.coq.run_stmt(tactic, timeout=self.coq_exec.timeout_in_sec)
        self.all_tactics.append(tactic)

        goals_after = len(self.coq_exec.coq.proof_context.fg_goals + self.coq_exec.coq.proof_context.bg_goals)

        # Strip goal label
        cur_goal = 1
        stripped_tactic = tactic
        match = re.match(r'(\d+)\s*:\s*([\s\S]+)', tactic)
        if not match == None: # Remove goal label from tactic
            cur_goal = int(match.group(1))
            stripped_tactic = match.group(2)

        # Process semicolons
        semicolon_ind = CoqLineByLineReader.splittable_semicolon(stripped_tactic)
        if semicolon_ind >= 0:
            # Cancel last tactic; process each segment individually
            self.coq_exec.coq.cancel_last()
            del self.all_tactics[-1]

            # Run first tactic
            first_tactic = str(cur_goal) + ":" + stripped_tactic[0:semicolon_ind] + "."
            self.parse_tactic(first_tactic)

            # Handle next tactics recursively
            new_goals = len(self.coq_exec.coq.proof_context.fg_goals + self.coq_exec.coq.proof_context.bg_goals)
            obls_added = new_goals - goals_before
            if obls_added > 0: # Handle branching
                remaining = stripped_tactic[semicolon_ind+1:].strip()

                oblig_start = cur_goal - 1
                oblig_end = cur_goal + obls_added

                next_tacs = []
                # depending on if remaining is "[ .. ]", change content of remaining
                if remaining[0] == '[':
                    token = ""
                    num_bracket = 0
                    for c in remaining[1:]:
                        if (c == '|' or c == ']') and num_bracket == 0:
                            complete_token = token.strip()
                            if complete_token[-1] not in '.]':
                                complete_token += '.'
                            next_tacs.append(complete_token)
                            token = ""
                        elif c == '[':
                            num_bracket+=1
                        elif c == ']':
                            num_bracket-=1
                        else:
                            token = token + c
                else:
                    for i in range(cur_goal - 1, oblig_end):
                        next_tacs.append(remaining)

                i = 0
                while oblig_start < oblig_end:
                    labeled_stmt = str(oblig_start+1) + ":" + next_tacs[i]
                    i += 1

                    self.parse_tactic(labeled_stmt)
                    n_goals = len(self.coq_exec.coq.proof_context.fg_goals + self.coq_exec.coq.proof_context.bg_goals)
                    obls_added = n_goals - new_goals
                    new_goals = n_goals

                    oblig_start += obls_added
                    oblig_end += obls_added

                    oblig_start += 1

            elif obls_added > -1: # Make sure this obligation hasn't already been solved
                # Run the rest of the tactic
                remaining = str(cur_goal) + ":" + stripped_tactic[semicolon_ind+1:].strip()
                self.parse_tactic(remaining)

    def run_in_loop(self):
        last_stmt = None
        flag = True

        while True:
            try:
                cmd_ran = self.coq_exec.run_next()
                last_stmt = self.coq_exec.current_stmt
                self.all_tactics.append(last_stmt)

                if self.coq_exec.is_in_proof_mode():
                    # Skip things that aren't true tactics
                    if flag or "".join(last_stmt.split()) in ["Proof.", "Qed.", "-", "+", "*", "--", "++", "**", "---", "+++", "***", "----", "++++", "****", "{", "}"]:
                        flag = False # Flag indicates the lemma statement, which is always the first "tactic"
                    else:
                        self.coq_exec.coq.cancel_last()
                        del self.all_tactics[-1]

                        # Strip goal label
                        cur_goal = 1
                        stripped_tactic = last_stmt
                        match = re.match(r'(\d+)\s*:\s*([\s\S]+)', last_stmt)
                        if not match == None: # Remove goal label from tactic
                            cur_goal = int(match.group(1))
                            stripped_tactic = match.group(2)
                        self.parse_tactic(str(cur_goal) + ":" + stripped_tactic)
                else:
                    flag = True

                if not cmd_ran:
                    break
            except:
                raise
            pass
        return self.all_tactics[:-1]

if __name__ == "__main__":
    os.chdir(root_dir)
    all_tactics = []
    with CoqSemicolonParser("coq-art/class.v", project_root = "coq-art/") as coq_exec:
        all_tactics = coq_exec.run_in_loop()

    print(all_tactics)