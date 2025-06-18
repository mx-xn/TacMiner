#!/usr/bin/env python3

import sys
import argparse
root_dir = f"{__file__.split('src')[0]}"
if root_dir not in sys.path:
    sys.path.append(root_dir)
import os
from io import TextIOWrapper
from typing import *
import json
import re

import utils
import coq_serapy
from coq_parser import CoqLineByLineReader
from coq_executor import CoqExecutor

class CoqCustomFileExec:
    def __init__(self, file_path: str = "src/resources/coq-conversion/SimpleAlgebra.v", project_root: str = None):
        self.coq_stdin_reader = CoqLineByLineReader(file_path)
        self.coq_exec : CoqExecutor = CoqExecutor(
            use_human_readable_proof_context=True, 
            proof_step_iter=self.coq_stdin_reader.instruction_step_generator(),
            project_root=project_root)
        self.failed_proofs = False
    
    def __enter__(self):
        self.coq_exec.__enter__()
        return self
    
    def __exit__(self, exc_type, exc_value, traceback):
        self.coq_exec.__exit__(exc_type, exc_value, traceback)

    def run_in_loop(self, out_file: TextIOWrapper, tactics, proof_dict, tac_dict):
        tactics_written = False
        proof_attempted = False

        while True:
            try:
                # Run next command
                cmd_ran = self.coq_exec.run_next()
                if not cmd_ran:
                    break
                
                lemma_name = self.coq_exec.get_current_lemma_name()
                lemma_statement1 = self.coq_exec.current_stmt
                if lemma_name in proof_dict:
                    if not proof_attempted:
                        proof_attempted = True

                        # if not tactics_written:
                        if lemma_name in tac_dict:
                            # Rewind and write custom tactics first

                            # Rewind
                            lemma_statement = self.coq_exec.current_stmt
                            self.coq_exec.rewind_proof_steps()

                            # Write custom tactics
                            # for tactic in tactics:
                            for tactic in tac_dict[lemma_name]:
                                out_file.write(tactic)
                                out_file.write("\n\n")
                                print(tactic)
                                self.coq_exec.coq.run_stmt(tactic, timeout=self.coq_exec.timeout_in_sec)
                            
                            # Restore
                            self.coq_exec.coq.run_stmt(lemma_statement, timeout=self.coq_exec.timeout_in_sec)
                            # tactics_written = True

                        lemma_statement = self.coq_exec.current_stmt

                        # Attempt to apply modified proof
                        test_proof = proof_dict[lemma_name][0]
                        proof_dict[lemma_name] = proof_dict[lemma_name][1:]
                        
                        try:
                            # Apply contracted proof

                            coq_reader = CoqLineByLineReader(file_content=test_proof.strip())
                            for idx, instruction in enumerate(coq_reader.instruction_step_generator()):
                                tac = instruction.strip()
                                if tac:
                                    print(tac)
                                    self.coq_exec.coq.run_stmt(tac, timeout=self.coq_exec.timeout_in_sec)

                            # Skip the original proof
                            self.coq_exec.run_lemma_without_executing()
                            # Output
                            out_file.write(lemma_statement)
                            out_file.write("\n")
                            out_file.write(test_proof)
                            out_file.write("\n\n")

                            proof_attempted = False
                            continue
                        except:
                            # Failed: use original proof
                            self.failed_proofs = True
                            print(f"\n\nProof is invalid: {self.coq_exec.current_stmt}\n{test_proof}")
                            # self.coq_exec.coq.cancel_last()
                            self.coq_exec.rewind_proof_steps()
                            self.coq_exec.coq.run_stmt(lemma_statement1, timeout=self.coq_exec.timeout_in_sec)

                # Output
                out_file.write(self.coq_exec.current_stmt)
                if not self.coq_exec.is_in_proof_mode():
                    proof_attempted = False
                    out_file.write("\n\n")
                else:
                    out_file.write(" ")
            except:
                raise

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run the script with specific filename")

    # Add arguments for bench_repo and filename
    parser.add_argument('--filename', type=str, required=True, help='The filename to process')
    parser.add_argument('--domain', type=str, required=True, help='The BM root repo to access')

    # Parse the arguments
    args = parser.parse_args()

    # Access the command-line arguments
    filename = args.filename
    bench_repo = args.domain
    os.chdir(root_dir)

    # bench_repo = "coq-art"
    # filename = "exo_frac1"
    # bench_repo = "atpl"
    # bench_repo = "CompCert"
    # filename = "CSL1"
    with open("src/resources/compression-eval/baseline-input/"+bench_repo+"/"+filename+"_tacs.txt", 'r') as fd:
        file_content = fd.read().split("-----")

    # Parsing
    in_file = file_content[0].strip()
    out_file = file_content[1].strip()
    tactics = file_content[2].strip().split("\n")
    proofs = file_content[3].strip().split("\n")

    proof_dict = {}
    for i in range(len(proofs)):
        if i % 2 == 0:
            proof_dict[proofs[i]] = []

    for i in range(len(proofs)):
        if i % 2 == 0:
            proof_dict[proofs[i]].append(proofs[i+1])

    # get the tactics for each proof
    new_pdict = {}
    tac_dict = {}
    relevant_tacs = []

    for name in proof_dict:
        if "Ltac" in name:
            relevant_tacs.append(name)
        else:
            # current is a proof
            if len(relevant_tacs) != 0:
                tac_dict[name] = relevant_tacs
                relevant_tacs = []
            new_pdict[name] = proof_dict[name]

    if in_file.startswith("CompCert/"):
        project_root = "CompCert/"
    elif in_file.startswith("cdf/"):
        project_root = "cdf/"
    elif in_file.startswith("bignums/"):
        project_root = "bignums/"
    elif in_file.startswith("coq-art/"):
        project_root = "coq-art/"
    else:
        project_root = None

    with CoqCustomFileExec(in_file, project_root = project_root) as coq_exec:
        with open(out_file, 'w') as fd:
            # coq_exec.run_in_loop(fd, tactics, proof_dict)
            coq_exec.run_in_loop(fd, tactics, new_pdict, tac_dict)
        with open("src/resources/compression-eval/baseline-input/"+bench_repo+"/"+filename+"_tacs_verified.txt", 'w') as fd:
            fd.write("F" if coq_exec.failed_proofs else "T")
        # with open("src/resources/maxsat/tacticList_verified.txt", 'w') as fd:
        #     fd.write("F" if coq_exec.failed_proofs else "T")
