# copra
COPRA: An in-COntext PRoof Agent which uses LLMs like GPTs to prove theorems in formal languages.

## Setup Steps:
1. Install OCaml first. Use the instructions here: https://opam.ocaml.org/doc/Install.html . The opam version used in this project is 2.1.3 (OCaml 4.14.0). Note that OCaml officially only supports Linux installations. One can use WSL on Windows machines.

2. Run the following to install Coq on Linux. The Coq version used in this project is <= 8.15. 
```
sudo apt install build-essential unzip bubblewrap
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```

3. Add the following to your `.bashrc` file: (sometimes the path `~/.opam/default` might not exist, so use the directory with version number present in the `~/.opam` directory)
```
export PATH="/home/$USER/.opam/default/bin:$PATH"
```

4. Create a `Miniconda` environment and activate it.


5. Change to the project root directory, and run the setup script i.e. `./src/scripts/setup.sh` from the root directory.

6. Add the following to your `.bashrc` file for Lean:
```
export PATH="/home/$USER/.elan/bin:$PATH"
```

7. You need to create a file `.secrets/openai_key.json` in the root directory of the project with the OpenAI API key. The file should contain the following:
```
{
    "organization": "<your-organization-id>",
    "api_key": "<your-api-key>"
}
```

8. The experiments are not necessarily thread safe. So, it is recommended to run them sequentially. The commands to run the desired experiments can be found in the file `./src/main/config/experiments.yaml`.

## Running Lean 4:

To run Lean 4 test you need to run additional steps:
1. Make sure to fetch the REPL submodule in `src/tools/repl`.
2. Build the REPL module using `lake build repl`.
3. Build the test repository by changing directory to `data/test/lean4_proj` and run `lake build`. (Note: For the first time it will take longer)
4. From the repository's root folder run `python src/main/eval_benchmark.py --config-name lean4_simple_experiment`

## Paper:
You can cite our paper:
```
@inproceedings{thakur2024context,
  title={An in-context learning agent for formal theorem-proving},
  author={Thakur, Amitayush and Tsoukalas, George and Wen, Yeming and Xin, Jimmy and Chaudhuri, Swarat},
  booktitle={First Conference on Language Modeling},
  year={2024}
}
```
Our paper can be found here: [OpenReview](https://openreview.net/forum?id=V7HRrxXUhN#discussion) and [ArXiv](https://arxiv.org/abs/2310.04353)
