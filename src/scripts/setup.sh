if [[ ! -d "src/scripts" ]]; then
    # Raise an error if the scripts directory is not present
    echo "Please run this script from the root of the repository, cannot find src/scripts"
    exit 1
fi
# Don't run without activating conda
# Check if Conda is activated
conda_status=$(conda info | grep "active environment" | cut -d ':' -f 2 | tr -d '[:space:]')
if [[ $conda_status == "None" ]] || [[ $conda_status == "base" ]]; then
    echo "Please activate conda environment before running this script"
    exit 1
fi
echo "Setting up TacMiner ..."
conda install pip
conda_bin=$(conda info | grep "active env location" | cut -d ':' -f 2 | tr -d '[:space:]')
pip_exe="$conda_bin/bin/pip"
ls -l $pip_exe
echo "Installing dependencies..."

echo "Installing OCaml (opam)..."
opam init -a --compiler=4.13.1
opam switch create 4.13.1
eval `opam config env`
opam update
# For Coq:
echo "Installing Coq..."
opam pin add coq 8.15.2
opam pin -y add menhir 20190626
# For SerAPI:
echo "Installing SerAPI (for interacting with Coq from Python)..."
opam install -y coq-serapi
echo "Installing Dpdgraph (for generating dependency graphs)..."
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq-dpdgraph
opam install -y coq-equations

# Python dependencies
echo "Installing Python dependencies..."
$pip_exe install --user -r requirements.txt
echo "Updating all git submodules..."
git submodule update --init --recursive
$pip_exe install --user -r src/python/coq_serapy/requirements.txt
pushd src/python/coq_serapy
python3 setup.py install
popd
echo "Updated all git submodules successfully!"
echo "Coq's Setup complete!"

# Java setup

# echo "Installing Java modules..."
# mkdir -p lib/graphstream
# pushd lib/graphstream
# wget https://github.com/graphstream/gs-core/releases/download/2.0/gs-core-2.0.jar
# wget https://github.com/graphstream/gs-algo/releases/download/2.0/gs-algo-2.0.jar
# wget https://github.com/graphstream/gs-ui-swing/releases/download/2.0/gs-ui-swing-2.0.jar
# popd
# pushd lib
# wget https://repo1.maven.org/maven2/org/junit/platform/junit-platform-console-standalone/1.10.2/junit-platform-console-standalone-1.10.2.jar
# wget https://repo1.maven.org/maven2/org/json/json/20240303/json-20240303.jar
# popd
# echo "Java setup complete!"

# Setup Open-WBO

# echo "Setting up Open-WBO..."
# pushd src/openwbo
# make r
# popd

echo "TacMiner's Setup complete!"