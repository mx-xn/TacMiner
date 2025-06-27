import argparse
import os
import re
import tempfile
import subprocess
import shutil
import json





class CoqScript:
    def __init__(self, file_path):
        self.file_path = os.path.abspath(file_path)
        self.lines = []
        self.theorems = {}  # {name: (start_line, end_line, body)}
        self.custom_tactics = {}  # {name: (start_line, end_line, body)}
        self.tactic_uses = {}  # {theorem_name: [tactic_names]}
        self.examples = {}  # {custom_tactic_name: list of examples taken from JSON}

        with open(self.file_path, 'r') as f:
            self.lines = f.readlines()

    def index_theorems(self):
        self.theorems = {}
        theorem_pattern = r'^(Lemma|Theorem|Example|Remark)\s+(\w+)'
        # theorem_pattern = r'^(Lemma|Theorem|Example|Remark)\s+(\w+)'
        in_theorem = False
        current_theorem = None
        start_line = None

        for i, line in enumerate(self.lines):
            line = line.strip()
            if not in_theorem:
                match = re.match(theorem_pattern, line)
                print("match is % s" % match)
                if match:
                    current_theorem = match.group(2)
                    start_line = i
                    in_theorem = True
            elif 'Qed.' in line:
                print("In qed, xurrent_thorems is %s" % current_theorem)
                self.theorems[current_theorem] = (start_line, i, self.lines[start_line:i+1])
                in_theorem = False

    def index_examples(self):
        for c in self.custom_tactics:
            self.examples[c] = extract_tactic_usage_examples(self.file_path, c)

    def index_tactics(self):
        self.custom_tactics = {}
        tactic_pattern = r'^Ltac\s+(\w+)'
        in_tactic = False
        current_tactic = None
        start_line = None

        for i, line in enumerate(self.lines):
            print("in line %s, in_tactic: %s" % (line, str(in_tactic)))
            if not in_tactic:
                match = re.match(tactic_pattern, line)
                if match is None:
                    print("match is None")
                else:
                    print("match is %s" % match.group)
                if match:
                    current_tactic = match.group(1)
                    print(current_tactic)
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

    def index(self):
        self.index_theorems()
        self.index_tactics()
        self.index_tactic_uses()
        self.index_examples()

    def clone(self):
        new_script = CoqScript(self.file_path)
        new_script.lines = self.lines.copy()
        new_script.theorems = self.theorems.copy()
        new_script.custom_tactics = self.custom_tactics.copy()
        new_script.tactic_uses = self.tactic_uses.copy()
        return new_script

    def parse_tactic_definition(self, tactic_def):
        # Split the definition into left-hand side (LHS) and right-hand side (RHS)
        lhs, rhs = tactic_def.split(':=', 1)

        # Extract tactic name and parameters from LHS
        parts = lhs.split()
        tactic_name = parts[1]  # Assuming 'Ltac' is parts[0]
        params = parts[2:] if len(parts) > 2 else []
        impl = rhs.strip()

        return tactic_name, params, impl

    def inline_tactics(self):
        inlined_lines = []
        tactic_definitions = {name: ''.join(body).strip() for name, (_, _, body) in self.custom_tactics.items()}

        # Parse all tactic definitions
        parsed_tactics = {}
        for tactic_def in tactic_definitions.values():
            name, params, impl = self.parse_tactic_definition(tactic_def)
            parsed_tactics[name] = (params, impl)

        for line in self.lines:
            if line.strip().startswith('Ltac'):
                # Skip Ltac definitions in the inlined version
                continue

            for tactic_name, (params, impl) in parsed_tactics.items():
                # Create a pattern to match the tactic usage
                tactic_pattern = rf'\b{re.escape(tactic_name)}\b((?:\s+[^\.;]+)*?)\.'

                def replace_tactic(match):
                    print('Match:', match.group(0))
                    args = match.group(1).strip()
                    tactic_impl = impl

                    # If there are arguments, replace them in the tactic implementation
                    if args:
                        arg_list = args.split()
                        for param, arg in zip(params, arg_list):
                            tactic_impl = re.sub(rf'\b{param}\b', arg, tactic_impl)

                    return tactic_impl

                # Replace all occurrences of the tactic in the line
                fixpoint = False
                changed = False

                while not fixpoint:
                    line_after = re.sub(tactic_pattern, replace_tactic, line)
                    if line_after == line:
                        fixpoint = True
                    else:
                        changed = True
                        line = line_after

                if changed:
                    print('Line before:', line)
                    print('Line after:', line_after)
                    line = line_after

            inlined_lines.append(line)

        return inlined_lines

    def write_inlined(self, output_path):
        inlined_content = self.inline_tactics()
        with open(output_path, 'w') as f:
            f.writelines(inlined_content)
        print(f"Inlined version written to: {output_path}")

    def check(self):
        try:
            with open(self.file_path, 'w') as temp_file:
                temp_file.writelines(self.lines)
                temp_file_path = temp_file.name
            result = subprocess.run(['make'], cwd=os.path.dirname(self.file_path), capture_output=True, text=True)
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

    def print_custom_tactics(self):
        print(f"Custom tactics found in {self.file_path}:")
        for tactic_name, (start, end, body) in self.custom_tactics.items():
            print(f"\n--- {tactic_name} ---")
            print(''.join(body).strip())
        print('Total:', len(self.custom_tactics))


    def print_custom_tactic_usage(self):
        theorems_with_tactics = {
            theorem: tactics
            for theorem, tactics in self.tactic_uses.items()
            if tactics
        }

        if not theorems_with_tactics:
            return

        # Print in YAML format, for use in COPRA config files.
        rel_path = os.path.relpath(self.file_path)
        print(f"- path: {rel_path}")
        print("  theorems:")
        for theorem, tactics in sorted(theorems_with_tactics.items()):
            print(f"    - {theorem} # {', '.join(sorted(tactics))}")

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

            undeclared_tactics = []
            for tactic in set(new_script.tactic_uses.get(theorem_name, [])):
                if tactic not in self.custom_tactics and tactic in new_script.custom_tactics:
                    undeclared_tactics.append(tactic)

            print('Undeclared tactics:', undeclared_tactics)

            tactic_bodies = []
            for tactic in undeclared_tactics:
                tactic_body = new_script.custom_tactics[tactic][2]
                tactic_bodies.extend(tactic_body)

            new_body = tactic_bodies + new_body

            temp_script = self.replace(theorem_name, new_body)

            if temp_script.check():
                print(f"Successfully replaced theorem '{theorem_name}'")
                self.lines = temp_script.lines
                self.index()
                successful_replacements += 1
            else:
                print(f"Failed to replace theorem '{theorem_name}'. Skipping.")
                unchanged_theorems += 1

        with open(self.file_path, 'w') as f:
            f.writelines(self.lines)

        print(f"\nRefactoring complete.")
        print(f"Theorems successfully replaced: {successful_replacements}")
        print(f"Theorems left unchanged: {unchanged_theorems}")
        print(f"Refactored file saved as: {self.file_path}")


def update_tactic_index(scripts, tactic_index_file, disable=False):
    disable = False
    result = {
        "theorem_file": {},
        "custom_tactics": {},
    }

    if not disable:
        print("not disable")
        for script in scripts:
            print("indexing script % s" % script)
            for theorem_name in script.theorems:
                print(theorem_name)
                result["theorem_file"][theorem_name] = script.file_path

            theorem_tactics = {}
            for theorem_name, (start, _, _) in script.theorems.items():
                tactics_before_theorem = []
                for tactic_name, (tactic_start, _, tactic_body) in script.custom_tactics.items():
                    if tactic_start < start:
                        tactics_before_theorem.append({
                            'name': tactic_name,
                            'definition': ''.join(tactic_body)
                        })
                theorem_tactics[theorem_name] = {
                    'available_tactics': tactics_before_theorem,
                    'examples': {
                        t['name']: script.examples[t['name']] for t in tactics_before_theorem
                    },
                    'used_tactics': script.tactic_uses.get(theorem_name, [])
                }
            result["custom_tactics"][script.file_path] = theorem_tactics

    # Load existing index data if the file exists
    if os.path.exists(tactic_index_file):
        if disable:
            existing_data = {}
        else:
            with open(tactic_index_file, 'r') as f:
                existing_data = json.load(f)

        # Update existing data with new data
        existing_data["theorem_file"].update(result["theorem_file"])
        existing_data["custom_tactics"].update(result["custom_tactics"])
        result = existing_data

    with open(tactic_index_file, 'w') as f:
        json.dump(result, f, indent=2)


def extract_tactic_usage_examples(script_path, tactic_name) -> list:
    json_path = script_path.replace(".v", '.json').replace("raw", "json")
    print("json_path:", json_path)
    with open(json_path) as f:
        trace_data = json.load(f)

    usage_examples = []

    for lemma in trace_data:
        lemma_name = lemma['lemma_name']

        for step in lemma['proof']:
            step_tactic_name = step['tactic_sig_no_out_arg'].split()[0]
            if step_tactic_name == tactic_name:
                usage_examples.append({
                    'lemma_name': lemma_name,
                    'tactic_sig': step['tactic_sig_no_out_arg'],
                    'tactic_args': step['tactic_args'],
                    'tactic_res': step['tactic_res']
                })

    return usage_examples


def main():
    parser = argparse.ArgumentParser(description="Coq script refactoring tool")
    parser.add_argument("--original", required=True, help="Path to the original Coq script")
    parser.add_argument("--new", help="Path to the new Coq script")
    parser.add_argument("--tactic-index", default="tactic_index.json", help="Path to the tactic index JSON file")
    parser.add_argument("--disable", action="store_true", help="Disable tactic indexing")
    parser.add_argument("--inline", action="store_true", help="Inline custom tactics")
    parser.add_argument("--index", action="store_true", help="Index scripts in a given directory.")
    parser.add_argument("--print-custom", action="store_true", help="Find and print custom tactic definitions")
    parser.add_argument("--print-uses-custom", action="store_true", help="Print theorems that use custom tactics")
    args = parser.parse_args()

    # if args.inline:
    #     original_script = CoqScript(args.original)
    #     output_path = os.path.splitext(args.original)[0] + ".inlined.v"
    #     original_script.write_inlined(output_path)
    #     return

    if args.index:
        dir = args.original
        scripts = []
        for root, _, files in os.walk(dir):
            for file in files:
                if file.endswith('.v'):
                    script = CoqScript(os.path.join(root, file))
                    script.index()
                    scripts.append(script)
        update_tactic_index(scripts, args.tactic_index, args.disable)
        return

    if args.print_uses_custom:
        if os.path.isdir(args.original):
            # Look for all Coq files in the tree
            for root, _, files in os.walk(args.original):
                for file in files:
                    if file.endswith('.v'):
                        script = CoqScript(os.path.join(root, file))
                        script.index()
                        script.print_custom_tactic_usage()
        else:
            script = CoqScript(args.original)
            script.index()
            script.print_custom_tactic_usage()
        return

    if args.print_custom:
        if os.path.isdir(args.original):
            # Look for all Coq files in the tree.
            for root, _, files in os.walk(args.original):
                for file in files:
                    if file.endswith('.v'):
                        script = CoqScript(os.path.join(root, file))
                        script.index()
                        print()
                        print('### Custom tactics in', script.file_path, ':')
                        script.print_custom_tactics()
        else:
            script = CoqScript(args.original)
            script.index()
            script.print_custom_tactics()
        return

    original_script = CoqScript(args.original)
    original_script.index()

    # print("Original script summary:")
    # original_script.summarize()

    # if args.new:
    #     new_script = CoqScript(args.new)
    #     new_script.index()
    #     print("\nStarting refactoring process...")
    #     original_script.refactor(new_script)

    # Update tactic index
    update_tactic_index([original_script], args.tactic_index, args.disable)
    print(f"Tactic index updated: {args.tactic_index}")


if __name__ == "__main__":
    main()