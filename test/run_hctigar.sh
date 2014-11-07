#!/bin/bash

PREFIX=$1
shift

for b in $(cat benchmarks)
do
    echo "Processing" $b "..."
    hctigar $b.bc $* > $PREFIX.$b.output
done
