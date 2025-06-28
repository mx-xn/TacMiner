java -jar tacminer.jar 1 coq-art SearchTree 3600 35
java -jar tacminer.jar 1 program-logics Separation 3600 35
java -jar tacminer.jar 1 bignums NMake 3600 35
java -jar tacminer.jar 1 comp-cert RegAlloc 3600 35

cd copra
cp index_files/tactic_index.json tactic_index.json
./runExp.sh bignums NMake