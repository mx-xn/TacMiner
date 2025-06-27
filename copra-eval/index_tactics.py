import os
import sys
import re
import json

def find_coq_files(directory):
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.v'):
                yield os.path.join(root, file)

def extract_custom_tactics(file_path):
    with open(file_path, 'r') as file:
        content = file.read()

    match = re.search(r'\(\*\* BEGIN_DREAMPROVER_TACTICS \*\*\)(.*?)\(\*\* END_DREAMPROVER_TACTICS \*\*\)', content, re.DOTALL)
    if not match:
        return {}

    tactic_block = match.group(1).strip()

    # Match lines like: Ltac custom0 H0 := tactic_body.
    # Supports optional arguments and multiline bodies
    tactic_defs = re.findall(r'Ltac\s+(\w+)[^:=]*:=\s*(.*?)(?=\nLtac|\Z)', tactic_block, re.DOTALL)

    # Create a dictionary mapping tactic names to definitions
    tactic_dict = {name: body.strip() for name, body in tactic_defs}
    return tactic_dict

    # match = re.search(r'\(\*\* BEGIN_DREAMPROVER_TACTICS \*\*\)(.*?)\(\*\* END_DREAMPROVER_TACTICS \*\*\)', content, re.DOTALL)
    # return match.group(1).strip() if match else None

def extract_theorems(file_path):
    with open(file_path, 'r') as file:
        content = file.read()

    theorems = re.findall(r'(Theorem|Lemma)\s+(\w+)\s*:', content)
    return [theorem[1] for theorem in theorems]




def main():
    if len(sys.argv) not in (2, 3):
        print("Usage: python script.py <directory> [--disable]")
        sys.exit(1)

    if sys.argv[1] == '--disable':
        result = {
            "theorem_file": {},
            "custom_tactics": {},
        }
    else:
        directory = sys.argv[1]
        theorem_file = {}
        custom_tactics = {}

        for file_path in find_coq_files(directory):
            print('doing', file_path)
            tactics = extract_custom_tactics(file_path)
            print('custom tactics:', tactics)
            if tactics:
                custom_tactics[file_path] = tactics
                theorems = extract_theorems(file_path)
                for theorem in theorems:
                    theorem_file[theorem] = file_path

        result = {
            "theorem_file": theorem_file,
            "custom_tactics": custom_tactics
        }

    with open('tactic_index.json', 'w') as f:
        json.dump(result, f, indent=2)

if __name__ == "__main__":
    main()