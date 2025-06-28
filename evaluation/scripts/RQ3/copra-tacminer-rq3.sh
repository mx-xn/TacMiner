# go to copra directory
cd copra

# coq-art
# switch the json files
cp index_files/tactic_index_chap5TM.json tactic_index.json
# Run the experiment
./runExp.sh coq_art_chap5_tacminer

cp index_files/tactic_index_chap11TM.json tactic_index.json
# Run the experiment
./runExp.sh coq_art_chap11_tacminer

cp index_files/tactic_index_parsingTM.json tactic_index.json
# Run the experiment
./runExp.sh coq_art_parsing_tacminer

cp index_files/tactic_index_impredicativeTM.json tactic_index.json
# Run the experiment
./runExp.sh coq_art_impredicative_tacminer

# comp-cert
switch the json files
cp index_files/tactic_index_AllocationTM.json tactic_index.json
# Run the experiment
./runExp.sh comp_cert_allocation_tacminer

cp index_files/tactic_index_NeedDomainTM.json tactic_index.json
# Run the experiment
./runExp.sh comp_cert_need_domain_tacminer

# bignums
# NMake
# switch the json files
cp index_files/tactic_index_NMakeTM.json tactic_index.json
# Run the experiment
./runExp.sh bignums_NMake_tacminer

# QMake
cp index_files/tactic_index_QMakeTM.json tactic_index.json
# Run the experiment
./runExp.sh bignums_QMake_tacminer

# ZMake
cp index_files/tactic_index_ZMakeTM.json tactic_index.json
# Run the experiment
./runExp.sh bignums_ZMake_tacminer