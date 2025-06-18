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

class CoqCustomFileExec:
    def __init__(self, file_path: str = "src/resources/coq-conversion/SimpleAlgebra.v", project_root: str = None):
        self.coq_stdin_reader = CoqLineByLineReader(file_path)
        self.coq_exec : CoqExecutor = CoqExecutor(
            use_human_readable_proof_context=True, 
            proof_step_iter=self.coq_stdin_reader.instruction_step_generator(),
            project_root=project_root)
    
    def __enter__(self):
        self.coq_exec.__enter__()
        return self
    
    def __exit__(self, exc_type, exc_value, traceback):
        self.coq_exec.__exit__(exc_type, exc_value, traceback)

    def run_in_loop(self):
        while True:
            try:
                cmd_ran = self.coq_exec.run_next()
                if not cmd_ran:
                    break
                # print(f"Coq> {self.coq_exec.current_stmt}")
            except:
                raise

if __name__ == "__main__":
    os.chdir(root_dir)

    with open("src/resources/maxsat/tacticList.txt", 'r') as fd:
        file_content = fd.read().split("\n")
    
    file_name = file_content[0]
    if file_name.startswith("CompCert/"):
        project_root = "CompCert/"
    else:
        project_root = None

    valid_tactics = []
    file_content = file_content[1:]
    with CoqCustomFileExec(file_name, project_root = project_root) as coq_exec:
        coq_exec.run_in_loop()
        for tac in file_content:
            if tac:
                try:
                    coq_exec.coq_exec.coq.run_stmt(tac, timeout=coq_exec.coq_exec.timeout_in_sec)
                    valid_tactics.append('T')
                except Exception as e:
                    valid_tactics.append('F')
                    print(f"Tactic {tac} failed to parse. Reason:")
                    print(e)
                    print("Skipping tactic...\n")

    with open("src/resources/maxsat/tacticList_verified.txt", 'w') as fd:
        fd.write("\n".join(valid_tactics))
