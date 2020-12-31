#!/bin/bash

# first two argument are start and end, third and fourth are weight k,j
args=($@)
echo $#
start=${args[0]}
end=${args[1]}
k=${args[2]}
j=${args[3]}

echo "start = " $start
echo "end = " $end
echo "k = " $k
echo "j = " $j

for (( idx=$start; idx<=$end; idx++ ))
do
  magma -b idx:=$idx k:=$k j:=$j lpolys_single_job.m &
done 
