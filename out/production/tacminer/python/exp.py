import os, sys, signal
import argparse
from multiprocessing import Process, Pool
from shlex import split
import subprocess
import time
import csv
import sys

def save_dict_to_csv(path, records):
    if len(records) == 0:
        return

    keys = records[0].keys()
    with open(path, "w") as output_file:
        dict_writer = csv.DictWriter(output_file, keys)
        dict_writer.writeheader()
        dict_writer.writerows(records)


def _parse_args():
    toolname = "toolname"
    parser = argparse.ArgumentParser(description=toolname)
    # benchmark argument:
    parser.add_argument("--bm_domain", type=str, dest="bm_domain", default="CompCert", help="benchmark domain set to run, can be so, CompCert, or any name as long as there exists a benchmark folder in /src/benchmarks/")
    parser.add_argument("--bm_topic", type=str, dest="bm_topic", default="all", help="if specified to 'all' then it'll run all the topics within the folder, otherwise it should be a string of the benchmark file")
    parser.add_argument("--mode", type=int, dest="mode", default="0", help=f"0: {toolname}, 1: Peano,  2: {toolname}-pruningABL, 3: {toolname}-grammarABL")

    parser.add_argument("--train_mode", type=bool, dest="train_mode", default=False, help="True if train-test split mode is on, off otherwise")
    parser.add_argument("--train_portion", type=int, dest="train_portion", default="50", help="train size percentage. Can range from (0, 100). Effective only when train_mode is on")
    parser.add_argument("--rand_sample", type=bool, dest="rand_sample", default=False, help="Train set random sampled if set to True.")

    # ----- benchmark independent arguments
    # parser.add_argument("--java_path", type=str, dest="java_path", default="../main/")
    parser.add_argument("--parallel", type=bool, dest='parallel', default=True)
    parser.add_argument("--cpath", type=str, dest="cpath", default="tacminer.jar")
    parser.add_argument("--timeout", type=int, dest="timeout", default=300, help="timeout in seconds. no timeout if timeout = -1")  # if timeout == -1 then no timeout
    parser.add_argument("--main", type=str, dest="main", default="dream-prover")
                
    
    # ------ only apply to so
    parser.add_argument("--processnum", type=int, dest="processnum", default=5, help=f"the number of process to parallel run {toolname}")

    args = parser.parse_args()

    args.dir = os.getcwd()
    if not args.train_mode:
        args.train_portion = 100

    args.mem_max = 64
    
    # args.java_path = "{}/{}".format(args.dir, "resnax")
    # args.bm_path = "{}/dream-prover/{}/{}".format(args.dir, args.benchmark, "benchmark")

    return args

class Run:
    def __init__(self, args):
        # self.topic = topic 
        self.args = args

    def parse_java_command(self):
        # bpath = '{}/{}'.format(self.args.benchmark_path, benchmark)

        java_command = 'exec java -Xmx{}G -jar {}.jar {} {} {} {} {} {}'.format(
                    str(self.args.mem_max),
                    self.args.main,

                    self.args.timeout,
                    self.args.mode,

                    self.args.bm_domain,
                    self.args.bm_topic,
                    self.args.train_portion,
                    self.args.rand_sample, 
            )

        return java_command

    def parse_normal(self, output, sketch):

        op = output.rsplit("`")

        record = {}
        record["b"] = self.benchmark
        record["rank"] = sketch[0]
        record["sketch"] = sketch[1]
        if "null" in op[0] or op[0] == "":
            record["p"] = "null"
            record["cost"] = 999999.0
            record["time"] = 999999.0
            record["regex"] = "null"
            record["gt"] = "false"
        else:
            record["p"] = op[0]
            record["cost"] = float(op[0].split(": ")[1])
            if record["cost"] == 0.0:
                record["time"] = 0.0
            else:
                record["time"] = float(op[2])
            record["regex"] = op[1]
            record["gt"] = op[3]


        # print(record)
        return record

    def run(self):
        print("Started")
        cmd = self.parse_java_command()
        try:
            # output = str(subprocess.check_output(cmd, shell=True, timeout=self.args.timeout))
            subprocess.run(cmd, shell=True)
            #print(output)
            print("Finished")
            # return self.parse_normal(output[2:-3], sketch)
        except subprocess.TimeoutExpired:
            print("Time out")
            record = {}
            # record["b"] = self.benchmark
            # record["rank"] = sketch[0]
            # record["sketch"] = sketch[1]
            # record["p"] = "timeout"
            # record["cost"] = 999999.0
            # record["time"] = self.args.timeout
            # record["regex"] = "null"
            # record["gt"] = "false"
            return record

def main():
    # given a set of sketch, invoke several process
    # if one process returns, kill the rest and return.
    # parse some argumetns
    args = _parse_args()
    # print(args)

    # read benchmark files
    # print(args.log_path)
    # os.system("rm -r \"{}\"".format(args.log_path))
    # os.system("mkdir -p \"{}\"".format(args.log_path))
    print("directory_path:" + args.dir)
    exclude = ["benchmark"]

    all_results = []
    worker = Run(args)
    worker.run()

    # for root, dirs, files in os.walk(args.benchmark_path, topdown=True):
    #     dirs[:] = [d for d in dirs if d not in exclude]
    #     for benchmark in files:
    #         # print(benchmark)
    #         if benchmark.startswith("."):
    #             continue

    #         if len(args.bm_files) > 0 and benchmark not in args.benchmark_to_run:
    #             continue

    #         worker = Run(benchmark, args)
    #         with Pool(args.processnum) as p:
    #             p.map(lambda _: worker.run(), [None] * args.processnum)
                # p.map(worker.run, )
                # results = p.map(worker.run, sketches)

            # if args.benchmark == "so":
            #     results = so_sort(results)
            # elif args.benchmark == "deepregex":
            #     results = deepregex_sort(results)

            # find top-k
        # output all_results
        # save_dict_to_csv('{}/{}'.format(args.log_path, 'all_results.csv'), all_results)

        # os.system('mv \"{0}\" \"{0}\"1'.format(args.log_path))

def deepregex_sort(results):
    # first sort by rank
    results = sorted(results, key = lambda i: i["rank"])

    # print(results)
    results = sorted(results, key = lambda i: i["time"])

    # print(results)

    return results

def so_sort(results):
    results = sorted(results, key = lambda i: i["time"])
    return results

if __name__ == '__main__':
    # os.system("ant -buildfile resnax/build.xml clean")
    # os.system("ant -buildfile resnax/build.xml resnax")
    main()
    print("exp.py ends")