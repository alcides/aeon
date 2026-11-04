import os
import subprocess
from sys import stderr
import pandas as pd
from os import listdir
from os.path import isfile, join

verilog_path = "benchmarks/custom_and_lut"

verilog_files = [f for f in listdir(
    verilog_path) if isfile(join(verilog_path, f))]
verilog_files = [files for files in verilog_files if files.count(".v") > 0]

choices = [(1, 60), (5, 120), (20, 120), (50, 180), (500, 300), (1000, 600)]

for name in verilog_files:
    for i in range(len(choices)):
        max_time = choices[i][1]
        K = choices[i][0]
        cmd = "timeout "+str(max_time)+" ./bnsynth.sh " + \
            name + " " + str(K)+" cnf "+"1"
        try:
            output = subprocess.check_output(
                cmd, stderr=subprocess.STDOUT, shell=True,
                universal_newlines=True)
        except subprocess.CalledProcessError as exc:
            print("Status : FAIL", exc.returncode, exc.output)
            continue
        else:
            print("Output: \n{}\n".format(output))
        f = open("experiments/check", "r")
        check = f.read()
        if check == "OK":
            break
