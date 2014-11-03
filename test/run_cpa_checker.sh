#!/bin/bash

for b in $(cat benchmarks);
do
    echo -n $b
    echo -n ' '
    timeout 500s /usr/bin/time -f '%e' cpa.sh -sv-comp13--combinations-predicate $b.cpachecker.c &> tmpresults
    if grep 'Verification result: TRUE' tmpresults > /dev/null
    then
	t=$(tail -n 1 tmpresults)
	echo $t
    else
	echo 'ERR'
    fi
done
    
