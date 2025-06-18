import argparse
import os
import re
import tempfile
import subprocess
import shutil

class CoqScript:
    def __init__(self, file_path):
        self.file_path = os.path.abspath(file_path)
        self.lines = []
        self.theorems = {}  # {name: (start_line, end_line, body)}
        self.custom_tactics = {}  # {name: (start_line, end_line, body)}
        self.tactic_uses = {}  # {theorem_name: [tactic_names]}

        with open(self.file_path, 'r') as f:
            self.lines = f.readlines()

    def index_theorems(self):
        self.theorems = {}
        theorem_pattern = r'^\s*(Lemma|Theorem|Example|Remark)\s+((\w|\'|\d)+)'
        in_theorem = False
        current_theorem = None
        start_line = None

        for i, line in enumerate(self.lines):
            if not in_theorem:
                match = re.match(theorem_pattern, line)
                if match:
                    current_theorem = match.group(2).strip()
                    start_line = i
                    in_theorem = True
            elif 'Qed.' in line:
                self.theorems[current_theorem] = (start_line, i, self.lines[start_line:i+1])
                in_theorem = False

    def index_tactics(self):
        self.custom_tactics = {}
        tactic_pattern = r'^Ltac\s+(\w+)'
        in_tactic = False
        current_tactic = None
        start_line = None

        for i, line in enumerate(self.lines):
            if not in_tactic:
                match = re.match(tactic_pattern, line)
                if match:
                    current_tactic = match.group(1)
                    start_line = i
                    in_tactic = True
                    # One-line tactic definition.
                    if line.strip().endswith('.'):
                        self.custom_tactics[current_tactic] = (start_line, i, [line])
                        in_tactic = False
            elif line.strip().endswith('.'):
                self.custom_tactics[current_tactic] = (start_line, i, self.lines[start_line:i+1])
                in_tactic = False

    def index_tactic_uses(self):
        self.tactic_uses = {}
        for theorem, (start, end, _) in self.theorems.items():
            used_tactics = set()
            for tactic in self.custom_tactics:
                pattern = r'\b' + re.escape(tactic) + r'\b'
                for line in self.lines[start:end]:
                    if re.search(pattern, line):
                        used_tactics.add(tactic)
            self.tactic_uses[theorem] = list(used_tactics)
        
        for custom, (start, end, body) in self.custom_tactics.items():
            used_tactics = set()
            for tactic in self.custom_tactics:
                if tactic == custom:
                    continue
                pattern = r'\b' + re.escape(tactic) + r'\b'
                for line in self.lines[start:end+1]:
                    if re.search(pattern, line):
                        used_tactics.add(tactic)
            self.tactic_uses[custom] = list(used_tactics)

    def index(self):
        self.index_theorems()
        self.index_tactics()
        self.index_tactic_uses()

    def clone(self):
        new_script = CoqScript(self.file_path)
        new_script.lines = self.lines.copy()
        new_script.theorems = self.theorems.copy()
        new_script.custom_tactics = self.custom_tactics.copy()
        new_script.tactic_uses = self.tactic_uses.copy()
        return new_script

    def check(self):
        #with tempfile.NamedTemporaryFile(mode='w', suffix='.v', dir=os.path.dirname(self.file_path), delete=False) as temp_file:
        #    temp_file.writelines(self.lines)
        #    temp_file_path = temp_file.name

        try:
            with open(self.file_path, 'w') as temp_file:
                temp_file.writelines(self.lines)
                temp_file_path = temp_file.name

            if "CompCert" in self.file_path: 
                cwd = self.file_path[:self.file_path.index("CompCert") + 9]
            else:
                cwd = self.file_path.rsplit('/', 1)[0]
            result = subprocess.run(['make'], cwd=cwd, capture_output=True, text=True)
            if not result.returncode == 0:
                print(result)
            return result.returncode == 0
        except Exception as e:
            print(f"Error: {e}")
            return False

    def replace(self, theorem_name, new_theorem_body):
        new_script = self.clone()
        if theorem_name in new_script.theorems:
            start, end, _ = new_script.theorems[theorem_name]
            new_script.lines[start:end+1] = new_theorem_body
            new_script.index()
        return new_script

    def summarize(self):
        print(f"Summary for {self.file_path}")
        print("Custom tactics:")
        for tactic in self.custom_tactics:
            print(f"  - {tactic}")
        print("\nTheorems and their tactic usage:")
        for theorem, tactics in self.tactic_uses.items():
            print(f"  - {theorem}: {', '.join(tactics) if tactics else 'No custom tactics used'}")

    def backup(self):
        backup_path = f"{os.path.splitext(self.file_path)[0]}.orig.v"
        shutil.copy2(self.file_path, backup_path)
        print(self.file_path, f"backup saved as: {backup_path}")

    def restore(self, ignore_errors=True):
        orig_path = f"{os.path.splitext(self.file_path)[0]}.orig.v"
        if ignore_errors and not os.path.exists(orig_path):
            print(f"Error: Original file not found at {orig_path}. Skipping restore.")
            return
        shutil.copy2(orig_path, self.file_path)
        with open(self.file_path, 'r') as f:
            self.lines = f.readlines()
            self.index()
        print(f"Restored {self.file_path} to its original contents.")

    def refactor(self, new_script):
        successful_replacements = 0
        unchanged_theorems = 0

        self.backup()

        if self.check():
            print("Original script compiles successfully.")
        else:
            print("Error: Original script does not compile. Refactoring aborted.")
            return

        for theorem_name, (start, end, new_body) in new_script.theorems.items():
            if theorem_name not in self.theorems:
                print(f"Warning: Theorem '{theorem_name}' not found in the original script. Skipping.")
                unchanged_theorems += 1
                continue

            # Find undeclared tactics
            undeclared_tactics = []
            for tactic in set(new_script.tactic_uses.get(theorem_name, [])):
                if tactic not in self.custom_tactics and tactic in new_script.custom_tactics:
                    undeclared_tactics.append(tactic)

            last_sz = -1
            while len(undeclared_tactics) > last_sz:
                last_sz = len(undeclared_tactics)
                for custom in undeclared_tactics:
                    for tactic in set(new_script.tactic_uses.get(custom, [])):
                        if tactic not in self.custom_tactics and tactic in new_script.custom_tactics and tactic not in undeclared_tactics:
                            undeclared_tactics.append(tactic)

            undeclared_tactics = list(reversed(undeclared_tactics))
            print('Undeclared tactics:', undeclared_tactics)

            # Insert new tactic definitions right before the theorem
            tactic_bodies = []
            for tactic in undeclared_tactics:
                tactic_body = new_script.custom_tactics[tactic][2]
                tactic_bodies.extend(tactic_body)

            new_body = tactic_bodies + new_body

            # Replace theorem body
            temp_script = self.replace(theorem_name, new_body)

            # Check if the new script compiles
            if temp_script.check():
                print(f"Successfully replaced theorem '{theorem_name}'")
                self.lines = temp_script.lines
                self.index()
                successful_replacements += 1
            else:
                print(f"Failed to replace theorem '{theorem_name}'. Skipping.")
                unchanged_theorems += 1

        # Save the new file
        with open(self.file_path, 'w') as f:
            f.writelines(self.lines)

        print(f"\nRefactoring complete.")
        print(f"Theorems successfully replaced: {successful_replacements}")
        print(f"Theorems left unchanged: {unchanged_theorems}")
        print(f"Refactored file saved as: {self.file_path}")

def main():
    parser = argparse.ArgumentParser(description="Coq script refactoring tool")
    parser.add_argument("--original", required=True, help="Path to the original Coq script")
    parser.add_argument("--new", required=True, help="Path to the new Coq script")
    args = parser.parse_args()

    original_script = CoqScript(args.original)
    original_script.restore()

    new_script = CoqScript(getattr(args, 'new'))

    original_script.index()
    new_script.index()

    print("Original script summary:")
    original_script.summarize()
    print("\nNew script summary:")
    new_script.summarize()

    print("\nStarting refactoring process...")
    original_script.refactor(new_script)

if __name__ == "__main__":
    main()