#!/bin/bash
PROCESSES_TO_RUN=("batch_files/lpolys_single_1_1_3_0.m" \ 
"batch_files/lpolys_single_1_2_3_0.m" \ 
"batch_files/lpolys_single_1_3_3_0.m" \ 
"batch_files/lpolys_single_1_4_3_0.m" \ 
"batch_files/lpolys_single_1_1_4_0.m" \ 
"batch_files/lpolys_single_1_2_4_0.m" \ 
"batch_files/lpolys_single_1_1_5_0.m" \ 
"batch_files/lpolys_single_1_1_3_2.m" \ 
)
for i in ${PROCESSES_TO_RUN[@]}; do
	 magma -b ${i%/*}/./${i##*/} > ${i}.log 2>&1 &
done
