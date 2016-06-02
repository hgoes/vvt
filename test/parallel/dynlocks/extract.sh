#!/bin/bash

grep '^Total runtime:' $1 | sed 's/^Total runtime: \(.*\)s$/\1/'
