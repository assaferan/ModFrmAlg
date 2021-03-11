#!/bin/bash
PROCESSES_TO_RUN=("batch_files/lpolys_single_1_1_3_0.m" \ 
)
for i in ${PROCESSES_TO_RUN[@]}; do
	 magma -b ${i%/*}/./${i##*/} > ${i}.log 2>&1 &
done
