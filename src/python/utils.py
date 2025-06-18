import json
import subprocess

# Auxiliary class to parse sets in JSON
class SetEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, set):
            return list(obj)
        return json.JSONEncoder.default(self, obj)

class ParserAid:
    @staticmethod
    def get_arg_end_index(start, words):
        paren = 0
        for i in range(start, len(words)):
            if words[i] == '(':
                paren += 1
            else:
                if words[i] == ')':
                    paren -= 1
                if paren == 0:
                    return i + 1
        return -1

    @staticmethod
    def get_actual_and_sig_hyp(start, words, sig_words):
        end = ParserAid.get_arg_end_index(start, words)
        return (end, " ".join(words[start:end]), " ".join(sig_words[start:end]))


    @staticmethod
    def get_arg_replaced_sigs(arg_start, hyp, hyp_sig, tactic_args, tactic_sig, tactic_sig_no_outarg, hyp_name):
        print("hyp tac args", hyp, tactic_args)

        if hyp not in map(lambda x: x.split(" : ")[0], tactic_args):
        # if hyp not in map(lambda x: x.split(" : ")[0], tactic_args):
            print(hyp)
            count_i = hyp_sig.count("_i")
            args_append = [hyp_name + " : " + hyp] + tactic_args[arg_start + count_i:]
            tactic_args = tactic_args[0:arg_start] + args_append

            # print("new tac args:")
            for arg in tactic_args:
                print(arg)

            tactic_sig = tactic_sig.replace(hyp_sig, "_i")
            tactic_sig_no_outarg = tactic_sig_no_outarg.replace(hyp_sig, "_i")

        return (tactic_sig, tactic_sig_no_outarg, tactic_args)


class AutoRecorder:
    def __init__(self, path, filename):
        self.path = path
        self.filename = filename
        self.output = "src/resources/script-preprocess/" + filename[0:-2] + "_stdout.txt"
    def gather_stdout(self):
        # Define the command to run
        # cmd1 = "pwd"
        cmd = "coqc -R CompCert compcert " + self.path + self.filename

        # Run the command and capture its output
        try:
            result = subprocess.run(cmd, shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

            # Write the output to the file
            with open(self.output, "w") as f:
                f.write(result.stdout)
                f.write(result.stderr)  # If you want to include stderr in the output file

            print(f"The output of the command has been saved to {self.output}")
        except subprocess.CalledProcessError as e:
            print(f"An error occurred while running the command: {e}")
        with open(self.output, 'a') as file:
            file.write('(* info auto: *)\n')

    # return the nth signature of the auto tactic
    def get_nth_auto_implicit_sig(self, n):
        with open(self.output, 'r') as file:
            lines = file.readlines()

        # Find the indices of the markers
        marker = "(* info auto: *)"
        marker_indices = [index for index, line in enumerate(lines) if marker in line]

        if n <= 0 or n > len(marker_indices):
            raise ValueError("Invalid value for n. It should be between 1 and the number of markers in the file.")

        # Determine the start and end indices for the desired block
        start_index = marker_indices[n - 1] + 1
        end_index = marker_indices[n] if n < len(marker_indices) else len(lines)

        # Extract the block of text
        block = lines[start_index:end_index]

        return ''.join(block)