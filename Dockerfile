# Base image
FROM ubuntu:22.04

# Set environment
ENV DEBIAN_FRONTEND=noninteractive

# Install system packages
RUN apt-get update && apt-get install -y \
    curl \
    git \
    m4 \
    unzip \
    bubblewrap \
    build-essential \
    cmake \
    opam \
    software-properties-common \
    wget \
    libgmp-dev \
    libgtk2.0-0 \
    libx11-6 \
    libgl1 \
    libgl1-mesa-glx \
    python3 \
    python3-pip \
    pkg-config \
    vim \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

RUN apt-get update && apt-get install -y openjdk-17-jdk

# Install Miniconda
# Detect architecture & download appropriate installer
ENV CONDA_DIR=/opt/conda
RUN ARCH=$(dpkg --print-architecture) && \
    if [ "$ARCH" = "arm64" ] || [ "$ARCH" = "aarch64" ]; then \
        CONDA_URL=https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-aarch64.sh; \
    else \
        CONDA_URL=https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh; \
    fi && \
    curl -sSL $CONDA_URL -o /tmp/miniconda.sh && \
    bash /tmp/miniconda.sh -b -p $CONDA_DIR && \
    rm /tmp/miniconda.sh
ENV PATH=$CONDA_DIR/bin:$PATH

# Copy environment file and set up Conda env
COPY environment.yml /tmp/environment.yml

SHELL ["/bin/bash", "-c"]

RUN source /opt/conda/etc/profile.d/conda.sh && \
    conda env create -f /tmp/environment.yml && \
    conda clean --all --yes

# Activate the environment for later commands
SHELL ["conda", "run", "-n", "tacminer", "/bin/bash", "-c"]

# RUN /bin/bash -c "source /opt/conda/etc/profile.d/conda.sh && conda activate tacminer && bash ./src/scripts/setup.sh && cd copra && ./src/scripts/setup.sh"


# Install specific version of Coq via OPAM
RUN opam init --bare --disable-sandboxing --auto-setup -y && \
    opam switch create . ocaml-base-compiler.4.13.1 && \
    # load the switch into this shell
    . /root/.opam/opam-init/init.sh && \
    # assume system depexts (we already apt-installed pkg-config, libgmp-dev, ...)
    opam install -y --assume-depexts coq.8.15.2 && \
    opam clean

ENV PATH="/root/.opam/default/bin:$PATH"

# Set working directory
WORKDIR /tacminer

# Copy the code in
COPY . /tacminer

# Make sure your run.sh is executable
RUN chmod +x run.sh

# 1) Compile all .java under src/, using every .jar in lib/ for deps
RUN mkdir -p bin \
 && find src -name '*.java' -print \
    | xargs javac --release 17 -cp "lib/*" -d bin \
 && jar cfm tacminer.jar MANIFEST.MF -C bin . 

# Default command: exec your script directly
CMD ["bash", "run.sh"]
