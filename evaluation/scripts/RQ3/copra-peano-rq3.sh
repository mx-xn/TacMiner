# go to copra directory
cd copra

# # coq-art
# # switch the json files
cp index_files/tactic_index_chap5PN.json tactic_index.json
# Run the experiment
./runExp.sh coq_art_chap5_peano

cp index_files/tactic_index_chap11PN.json tactic_index.json
# Run the experiment
./runExp.sh coq_art_chap11_peano

cp index_files/tactic_index_parsingPN.json tactic_index.json
# Run the experiment
./runExp.sh coq_art_parsing_peano

cp index_files/tactic_index_impredicativePN.json tactic_index.json
# Run the experiment
./runExp.sh coq_art_impredicative_peano

# comp-cert
# switch the json files
# cp index_files/tactic_index_AllocationPN.json tactic_index.json
# # Run the experiment
# ./runExp.sh comp_cert_allocation_peano

# cp index_files/tactic_index_NeedDomainPN.json tactic_index.json
# # Run the experiment
# ./runExp.sh comp_cert_need_domain_peano

# bignums
# # NMake
# # switch the json files
# cp index_files/tactic_index_NMakePN.json tactic_index.json
# # Run the experiment
# ./runExp.sh bignums_NMake_peano

# # QMake
# cp index_files/tactic_index_QMakePN.json tactic_index.json
# # Run the experiment
# ./runExp.sh bignums_QMake_peano

# # ZMake
# cp index_files/tactic_index_ZMakePN.json tactic_index.json
# # Run the experiment
# ./runExp.sh bignums_ZMake_peano

# # ZMake
# mv tactic_index.json tactic_index_ph.json
# mv tactic_index_ZMakePN.json tactic_index.json
# # Run the experiment
# ./runExp.sh bignums_ZMake_peano
# mv tactic_index.json tactic_index_ZMakePN.json
# mv tactic_index_ph.json tactic_index.json
