#!/bin/bash

# the argument is the maximal analytic conductor
args=($@)
echo $#

N=${args[0]}

echo "N = " $N

magma -b N_an:=$N lpolys_10_box.m &

