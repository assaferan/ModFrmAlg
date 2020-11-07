#!/bin/bash

# first two argument are start and end, third is weight
args=($@)
echo $#
start=${args[0]}
end=${args[1]}
weight=${args[2]}

echo "start = " $start
echo "end = " $end
echo "weight = " $weight

for (( idx=$start; idx<=$end; idx++ ))
do
  magma -b idx:=$idx wt:=$weight lpolys_single_job.m &
done 
