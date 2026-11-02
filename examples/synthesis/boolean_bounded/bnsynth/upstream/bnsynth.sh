#!/bin/sh
python3 bnsynth.py \
--th=0.5 \
--P=0 \
--train=1 \
--tnorm_name=product \
--learning_rate=.01 \
--verilog_spec_location=custom_and_lut \
--verilog_spec=$1 \
--epochs=1 \
--batch_size=1 \
--K=$2 \
--preprocessor=1 \
--postprocessor=1 \
--architecture=$4 \
--layers=1 \
--cnf=$3 \
--ce=1 \
--load_saved_model=0 \
--output_file=out.csv
