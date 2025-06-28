# Code Artifact for TacMiner
Automated Discovery of Tactic Libraries for Interactive Theorem Proving

## Overview

This repository contains the code artifact supporting the evaluation section of the paper **"Automated Discovery of Tactic Libraries for Interactive Theorem Proving."** This artifact enables reproducibility of key experimental claims, specifically:

1. **TacMiner** learns significantly more (~3×) tactics than the anti-unification-based baseline (e.g., Peano), enabling more concise proofs. (Section 8.2)
2. **TacMiner** achieves higher proof corpus compression compared to the baseline. (Section 8.3)
3. Custom tactics discovered by TacMiner improve downstream proof automation, boosting success rates of automation tools like Copra by up to 172%. (Section 8.4)
4. **TacMiner** exhibits strong data efficiency, achieving significant compression with decreased size of training data. (Section 8.5)
5. Ablation studies validate the importance of grammar learning and pruning for tractable search and performance. (Section 8.6)

This artifact includes all necessary code, benchmarks, and scripts to reproduce our results. Due to some inherent randomness in the runs, exact numbers may vary slightly (especially for the proof automation experiment), but overall findings and conclusions remain consistent.

## Getting Started Guide

This artifact may be run via a prebuilt Docker image.

### Building and Running the Docker Image

Docker setup is recommended for consistency and ease. Allocate at least 64GB RAM and 4 CPU cores. It takes around 20 min for it to complete building.

```bash 
docker build -t tacminer:v1 .
docker run --rm -it tacminer:v1 bash
```

### Set-up
Once in the docker container, we have a few more setup steps to do (~ 7min):

```bash
# activate conda
source /opt/conda/etc/profile.d/conda.sh
conda activate tacminer

# run the tacminer + copra setup script
./src/scripts/setup.sh
cd copra
./src/scripts/setup.sh
cd ..
```

Steps to compile the necessary benchmarks:
```bash
# Source the opam initialization script
source /root/.opam/opam-init/init.sh

# Ensure opam binaries are in the PATH
export PATH="/root/.opam/default/bin:$PATH"

# script for compiling the benchmarks (~ 10min)
./setup.sh
```

Note: The CompCert compilation might partially fail, but by that point all the CompCert benchmarks necessary to the experiments should have been compiled.

To test successful setup, try running `./test.sh`. The run should finish in around 5-7 minutes. If everything stopped running without an error, then the setup is successful!

## Step-by-Step Instructions

### Reproducing Claim #1 (Section 8.2): 

- **Run TacMiner (~ 20min):**

   ```bash
   ./run.sh rq1 0

- **Run Peano baseline (~3hrs)**: 

   ```bash
    ./run.sh rq1 1

- Once both of the above finish running, format the results:

   ```bash
    ./run.sh rq1-format

See `evaluation/results/RQ1-tactics-stats/summary.txt` for the statistics and data needed to reproduce the findings from Section 8.2.

### Reproducing Claim #2 (Section 8.3): 

- **Run TacMiner (~ 3min):**
   ```bash
   ./run.sh rq2 0
- **Run Peano baseline (~ 70min)**:

   ```bash
    ./run.sh rq2 1

- Once both of the above finish running, format the results:

   ```bash
    ./run.sh rq2-format

See `evaluation/results/RQ2-compression-rate/summary.txt` for the compression rate data for Section 8.2.


### Reproducing Claim #3 (Section 8.4)

#### OpenAI Setup 
This section uses Copra, a GPT-based proof automation tool.  

To enable running Copra, add your OpenAI key to `copra/.secrets/openai_key.json`. 

- **Recommended:** Use the provided cache (default) for fast, stable results (since GPT outputs may vary across runs).
- **To run without cache:** 
To enable runs without cache, delete everything under `copra/.log/checkpoints`. (Or move them to somewhere else in case they are needed later.) The entire run (without cache) will likely take around a day.

#### Running the Experiments

This section evaluates proof automation results from:
1. Vanilla Copra
2. Copra + Peano (baseline)
3. Copra + TacMiner

Use the following commands:

```bash
# 1. Vanilla Copra
./run.sh rq3 0

# 2. Copra + Peano (baseline)
./run.sh rq3 1

# 3. Copra + TacMiner
./run.sh rq3 2
```

Format results after all runs:
```bash
./run.sh rq3-format
```

Note that these runs are not necessarily thread safe, so it is recommended to run them in sequence.

#### Results
See: `results/RQ3-proof-automation/summary.txt` for the summarized output.

If the user would like to view the detailed raw logs, they can be found under `copra/.log/evals/benchmark/<domain>_<tool>`.


### Reproducing Claim #4 (Section 8.5)
Section 8.5 examines how well TacMiner performs when less training data is available, reporting compression rates as training set size decreases.

#### How to Run

1. **Start the experiment: (~ 3hrs)**
   ```bash
   ./run.sh rq4

2. **Format the results:**
   ```bash
   ./run.sh format-rq4 

#### Outputs

- Tabular/text summary:

`./evaluation/RQ4-data-efficiency/summary.txt`

- Plot of results:

` ./evaluation/RQ4-data-efficiency/summary.png`

**Side Notes:**

If you want to view the plots generated, here are two recommended methods:

- Copy plots from the container to your host machine:

You can find the container ID by running `docker ps`, then transfer the plot file using:

`docker cp <containerID>:<plot>.png ./<local-dest>/plot.png`

- View plots directly inside the container using a terminal image viewer: 

Install a command-line image viewer like viu or chafa to preview images without leaving the terminal:

```bash
apt-get update && apt-get install -y chafa
chafa <plot>.png
```

### Reproducing Claim #5 (Section 8.6)

Section 8.6 evaluates the importance of both the pruning and grammar learning techniques used in TacMiner.  
We compare three settings:
- **Both pruning and grammar learning enabled (default)**
- **No pruning**
- **No grammar learning**

Experiments report the cumulative time to extract tactics in each configuration, broken down by domain.

#### Running the Experiments

To run each configuration:

```bash
# 1. Without pruning
./run.sh rq5 0

# 2. Without grammar learning
./run.sh rq5 1
```

##### Note on Memory Usage:

*The ablation experiments were run with a Java heap space limit of up to 16 GB, based on the default local JVM configuration. When you're running the ablation in Docker, and the container is allocated significantly less memory, you may encounter OutOfMemoryErrors.*

*This should not affect normal TacMiner runs, which have much lower memory requirements. If needed, you can set the Java heap size explicitly using -Xmx and adjust Docker memory allocation accordingly.*

After all runs complete, format the results:

```bash
./run.sh format-rq5
```

#### Viewing Results

For each domain (e.g., ProgramLogic, CompCert, CoqArt, etc.):

- Tabular/text summary: `./evaluation/RQ5-ablation/<domain>.txt`

- Plots: `./evaluation/RQ5-ablation/<domain>.png`

