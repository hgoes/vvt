#!/bin/bash

RUNS=$1
POST=$2
shift 2
until [ -z "$1" ]
do
    echo -n $1
    for i in `seq 0 $(($RUNS - 1))`
    do
	echo -en '\t'
	./extract.sh $1.$i.output-$POST | tr -d '\n'
    done
    echo
    shift
done
