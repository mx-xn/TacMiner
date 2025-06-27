# { time (cd copra && ./runExp.sh coq_art); } 2>> time-copra-coq_art.txt
# { time (cd copra && ./runExp.sh comp_cert_need_domain); } 2>> time-copra-comp_cert.txt
# { time (cd copra && ./runExp.sh comp_cert_allocation); } 2>> time-copra-comp_cert.txt
# { time (cd copra && ./runExp.sh bignums); } 2>> time-copra-bignums.txt

cd copra 
./runExp.sh comp_cert_need_domain
./runExp.sh comp_cert_allocation