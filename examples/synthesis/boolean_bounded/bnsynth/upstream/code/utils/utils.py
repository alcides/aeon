import argparse
import copy
import os
import signal
import tempfile
from math import floor
from subprocess import PIPE, Popen
from typing import OrderedDict

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import torch
from numpy import count_nonzero
from torch.utils.data import DataLoader, TensorDataset


class cexmodels:

    def __init__(self, modelx, modely, modelyp):
        self.modelx = modelx
        self.modely = modely
        self.modelyp = modelyp

# Utilities class


class utils():
    def __init__(self):
        self.name = "product"
        self.res = []
        super(utils, self).__init__()

    def negation(self, x):
        '''
        Fuzzy alternative for Logical NOT
        '''

        return 1 - x

    # Continuous AND with n inputs
    def tnorm_n_inputs(self, inp):
        '''
        Fuzzy alternative for Logical AND
        '''

        if self.name == "godel":
            out, _ = torch.min(inp, dim=-2)
            return out
        elif self.name == "product":
            return torch.prod(inp, -2)
        else:
            print("Wrong Name!")

    def add_noise(self, samples, range=0.1):
        '''
        Adds random noise to samples to generate fractional samples
        '''

        return torch.where(
            samples > 0.5,
            torch.rand(samples.shape)*range + (1 - range),
            torch.rand(samples.shape)*range
        )

    def make_arg_parser(self):
        '''
        Comman Line Argument Parser
        '''

        parser = argparse.ArgumentParser()
        parser.add_argument("--threshold", metavar="--th", type=float,
                            default=0.8, help="Enter value between 0.5 <= th <= 1")
        parser.add_argument("--no_of_input_var", metavar="--noiv",
                            type=int, default=1, help="Enter value >= 1")
        parser.add_argument("--K", type=int, default=10,
                            help="No. of Clauses >= 1")
        parser.add_argument("--epochs", type=int, default=50,
                            help="No. of epochs to train")
        parser.add_argument("--learning_rate", metavar="--lr",
                            type=float, default=0.01, help="Default 0.01")
        parser.add_argument("--batch_size", type=int,
                            default=32, help="Enter batch size")
        parser.add_argument("--tnorm_name", type=str,
                            default="product", help="godel/product")
        parser.add_argument("--P", type=int, default=0,
                            help="0: Regression, 1: Classification")
        parser.add_argument("--train", type=int, default=0,
                            help="1/0; 0 loads the saved model")
        parser.add_argument("--preprocessor",
                            type=int, default=1, help="1 for manthan1 2 for manthan2")
        parser.add_argument("--postprocessor",
                            type=int, default=1, help="1 for manthan1 2 for manthan2")
        parser.add_argument("--architecture",
                            type=int, default=1, help="1: Arch 1; 2: Arch 2; 3: Arch 3")
        parser.add_argument("--cnf",
                            type=str, default=1, help="1: for cnf; 0: for dnf")
        parser.add_argument("--ce",
                            type=int, default=0, help="1: run ce loop; 0: skip ce loop")
        parser.add_argument("--load_saved_model",
                            type=int, default=1, help="1: load moedl from saved checkpoint; 0: train from scratch")
        parser.add_argument("--verilog_spec", type=str,
                            default="sample1", help="Enter file name")
        parser.add_argument("--verilog_spec_location", type=str,
                            default="verilog", help="Enter file location")
        parser.add_argument("--output_file", type=str,
                            default="experiments.csv", help="Enter file name for storing results")
        parser.add_argument("--layers", type=int,
                            default=1, help="Enter no. of layers")

        return parser

    def plot(self):
        '''
        Plots losses against epochs
        '''

        f = open("train_loss", "r")
        train_loss = f.read().split(",")
        f.close()
        train_loss = [float(i) for i in train_loss]
        plt.plot(train_loss, label="train_loss")
        # f = open("valid_loss", "r")
        # valid_loss = f.read().split(",")
        # f.close()
        # valid_loss = [float(i) for i in valid_loss]
        # plt.plot(valid_loss, label="valid_loss")
        # plt.legend()
        f = open("accuracy_list", "r")
        accuracy_list = f.read().split(",")
        f.close()
        accuracy_list = [float(i) for i in accuracy_list]
        plt.plot(accuracy_list, label="accuracy")
        plt.savefig("train_valid_loss_plot.png")

    def convert_verilog(self, input, cluster):
        '''
        Converts qdimacs to verilog
        Input: qdimacs input file
        Output: verilog formula
        '''

        with open(input, 'r') as f:
            lines = f.readlines()
        f.close()
        itr = 1
        declare = 'module FORMULA( '
        declare_input = ''
        declare_wire = ''
        assign_wire = ''
        tmp_array = []

        for line in lines:
            line = line.strip(" ")
            if (line == "") or (line == "\n"):
                continue
            if line.startswith("c "):
                continue

            if line.startswith("p "):
                continue

            if line.startswith("a"):
                a_variables = line.strip("a").strip(
                    "\n").strip(" ").split(" ")[:-1]
                for avar in a_variables:
                    declare += "%s," % (avar)
                    declare_input += "input %s;\n" % (avar)
                continue

            if line.startswith("e"):
                e_variables = line.strip("e").strip(
                    "\n").strip(" ").split(" ")[:-1]
                for evar in e_variables:
                    tmp_array.append(int(evar))
                    declare += "%s," % (evar)
                    declare_input += "input %s;\n" % (evar)
                continue

            declare_wire += "wire t_%s;\n" % (itr)
            assign_wire += "assign t_%s = " % (itr)
            itr += 1

            clause_variable = line.strip(" \n").split(" ")[:-1]
            for var in clause_variable:
                if int(var) < 0:
                    assign_wire += "~%s | " % (abs(int(var)))
                else:
                    assign_wire += "%s | " % (abs(int(var)))

            assign_wire = assign_wire.strip("| ")+";\n"

            # Removed code for mutliclass as it's not needed in our case.

        count_tempvariable = itr

        declare += "out);\n"
        declare_input += "output out;\n"

        temp_assign = ''
        outstr = ''

        itr = 1
        while itr < count_tempvariable:
            temp_assign += "t_%s & " % (itr)
            if itr % 100 == 0:
                declare_wire += "wire tcount_%s;\n" % (itr)
                assign_wire += "assign tcount_%s = %s;\n" % (
                    itr, temp_assign.strip("& "))
                outstr += "tcount_%s & " % (itr)
                temp_assign = ''
            itr += 1

        if temp_assign != "":
            declare_wire += "wire tcount_%s;\n" % (itr)
            assign_wire += "assign tcount_%s = %s;\n" % (
                itr, temp_assign.strip("& "))
            outstr += "tcount_%s;\n" % (itr)
        outstr = "assign out = %s" % (outstr)

        verilogformula = declare + declare_input + \
            declare_wire + assign_wire + outstr + "endmodule\n"

        return verilogformula

    def make_dataset_larger(self, samples, N=100):
        '''
        Adds N points from the neighborhood of each sample point
        '''

        # tensor dataset
        training_samples = torch.from_numpy(samples)

        # add random noise to get fractional samples
        training_samples = torch.cat([
            self.add_noise((training_samples)) for _ in range(N)
        ])
        training_samples = training_samples.to(torch.double)

        return training_samples

    def prepare_io_dicts(self, total_vars):
        '''
        Prepares and returns io variable dictionary
        '''

        io_dict = {}
        for index, value in enumerate(total_vars):
            io_dict[index] = value
        io_dict = OrderedDict(io_dict)

        return io_dict

    def store_nn_output(self, num_of_outputs, skfunc):
        '''
        Stores the skolem function into file
        skfunc: skolem function
        '''

        open('nn_output', 'w').close()
        f = open("nn_output", "a")
        for i in range(num_of_outputs):
            if i < num_of_outputs-1:
                f.write(skfunc[i][:-1]+"\n")
            else:
                f.write(skfunc[i][:-1])
        f.close()

    def store_losses(self, train_loss, valid_loss, accuracy_list):
        '''
        stores losses into file
        '''

        f = open("train_loss", "w")
        train_loss = np.array(train_loss)
        train_loss.tofile(f, sep=",", format="%s")
        f.close()

        f = open("valid_loss", "w")
        valid_loss = np.array(valid_loss)
        valid_loss.tofile(f, sep=",", format="%s")
        f.close()

        f = open("accuracy_list", "w")
        accuracy_list = np.array(accuracy_list)
        accuracy_list.tofile(f, sep=",", format="%s")
        f.close()

    def store_preprocess_time(self,
                              verilog_spec, num_of_vars, num_out_vars, num_of_eqns, epochs, no_of_samples, preprocess_time
                              ):
        line = verilog_spec+","+str(num_of_vars)+","+str(num_out_vars)+","+str(
            num_of_eqns)+","+str(epochs)+","+str(no_of_samples)+","+str(preprocess_time)+"\n"
        f = open("preprocess_data.csv", "a")
        f.write(line)
        f.close()

    def get_var_indices(self, num_of_vars, output_varlist, io_dict):
        '''
        Creates list of indices of input and output variables
        Input: output varlist, input output dictionary
        Output: input_var_idx, and output_var_idx as index lists
        '''

        output_var_idx = [list(io_dict.values()).index(output_varlist[i]) for i in range(
            len(output_varlist)) if output_varlist[i] in io_dict.values()]
        var_indices = [i for i in range(num_of_vars)]
        input_var_idx = [x for x in var_indices if x not in output_var_idx]
        return input_var_idx, output_var_idx

    def get_train_test_split(self, dataset):
        '''
        Performs train test split of the dataset
        '''

        data_size = dataset.shape[0]
        val_size = floor(data_size*0.2)
        train_size = data_size - val_size
        validation_set = dataset[train_size:, :]
        training_set = dataset[:, :]

        return training_set, validation_set

    def get_skolem_function_cnf(self, args, gcln, no_of_input_var, input_var_idx, num_of_outputs, output_var_idx, io_dict):
        '''
        Reads the model weights (layer_or_weights, layer_and_weights) and builds the skolem function based on it.
        Input: Learned model parameters
        Output: Skolem Functions
        '''

        layer_or_weights_1 = gcln.layer_or_weights_1.cpu().detach().numpy()  # input_size x K
        layer_and_weights_1 = gcln.layer_and_weights_1.cpu(
        ).detach().numpy()  # K x num_of_outputs

        threshold = args.threshold
        K = args.K
        architecture = args.architecture

        literals = []
        neg_literals = []
        for i in input_var_idx:
            # literals.append(io_dict.get(i))
            # neg_literals.append("~"+io_dict.get(i))
            literals.append("i"+str(i))
            neg_literals.append("~i"+str(i))

        clause = np.array(literals + neg_literals)

        clauses = []
        if architecture == 1:
            for j in range(K):
                mask = layer_or_weights_1[:, j] > threshold
                clauses.append(clause[mask])
            clauses = np.array(clauses)
        elif architecture == 2:
            for j in range(K):
                mask = layer_or_weights_1[:, j] > threshold
                clauses.append(clause[mask])
            clauses = np.array(clauses)
        elif architecture == 3:
            for j in range(num_of_outputs * K):
                mask = layer_or_weights_1[:, j] > threshold
                clauses.append(clause[mask])
            clauses = np.array(clauses)

        ored_clauses = []
        for j in range(len(clauses)):
            ored_clauses.append("("+" | ".join(clauses[j])+")")
        ored_clauses = np.array(ored_clauses)

        gated_ored_clauses = []
        if architecture == 1:
            for i in range(num_of_outputs):
                mask = layer_and_weights_1[i*K:(i+1)*K, :] > threshold
                ored_clause = ored_clauses.reshape((-1, 1))[i*K:(i+1)*K, :]
                gated_ored_clauses.append(
                    np.unique(ored_clause[mask]))

        elif architecture == 2:
            for i in range(num_of_outputs):
                mask = layer_and_weights_1[:, i] > threshold
                ored_clause = ored_clauses.reshape((-1, 1))
                gated_ored_clauses.append(
                    np.unique(ored_clause[mask]))

        elif architecture == 3:
            for i in range(num_of_outputs):
                mask = layer_and_weights_1[i*K:(i+1)*K, :] > threshold
                ored_clause = ored_clauses.reshape((-1, 1))[i*K:(i+1)*K, :]
                gated_ored_clauses.append(
                    np.unique(ored_clause[mask]))

        skfs = []
        for i in range(num_of_outputs):
            skf = " & ".join(gated_ored_clauses[i])+"\n"
            if " & ()" in skf:
                skf = skf.replace(" & ()", "")
            if "() & " in skf:
                skf = skf.replace("() & ", "")
            skfs.append(skf)

        return skfs

    def read_cnf(self, threshold, architecture, layer_or_weights, layer_and_weights, hidden_size, num_of_outputs, K, clause):
        clauses = []
        if architecture == 1:
            for j in range(K):
                mask = layer_or_weights[:, j] > threshold
                clauses.append(list(clause[mask]))
            clauses = np.array(clauses, dtype=list)
        elif architecture == 2:
            for j in range(hidden_size):
                mask = layer_or_weights[:, j] > threshold
                clauses.append(list(clause[mask]))
            clauses = np.array(clauses, dtype=list)
        elif architecture == 3:
            for j in range(num_of_outputs * K):
                mask = layer_or_weights[:, j] > threshold
                clauses.append(list(clause[mask]))
            clauses = np.array(clauses, dtype=list)

        ored_clauses = []
        for j in range(len(clauses)):
            ored_clauses.append("("+" | ".join(clauses[j])+")")
        ored_clauses = np.array(ored_clauses)

        gated_ored_clauses = []
        if architecture == 1:
            for i in range(layer_and_weights.shape[1]):
                mask = layer_and_weights[:, i] > threshold
                ored_clause = ored_clauses.reshape((-1, 1))
                gated_ored_clauses.append(
                    np.unique(ored_clause[mask]))

            skfs = []
            for i in range(layer_and_weights.shape[1]):
                skf = "("+" & ".join(gated_ored_clauses[i])+")"
                if " & ()" in skf:
                    skf = skf.replace(" & ()", "")
                if "() & " in skf:
                    skf = skf.replace("() & ", "")
                skfs.append(skf)

        elif architecture == 2:
            for i in range(num_of_outputs):
                mask = layer_and_weights[:, i] > threshold
                ored_clause = ored_clauses.reshape((-1, 1))
                # print("shape: ", mask.shape, ored_clause.shape)
                gated_ored_clauses.append(
                    np.unique(ored_clause[mask]))

            skfs = []
            for i in range(layer_and_weights.shape[1]):
                skf = "("+" & ".join(gated_ored_clauses[i])+")"
                if " & ()" in skf:
                    skf = skf.replace(" & ()", "")
                if "() & " in skf:
                    skf = skf.replace("() & ", "")
                skfs.append(skf)

        elif architecture == 3:
            for i in range(num_of_outputs):
                mask = layer_and_weights[i*K:(i+1)*K, :] > threshold
                ored_clause = ored_clauses.reshape((-1, 1))[i*K:(i+1)*K, :]
                gated_ored_clauses.append(
                    np.unique(ored_clause[mask]))

            skfs = []
            for i in range(num_of_outputs):
                skf = "("+" & ".join(gated_ored_clauses[i])+")"
                if " & ()" in skf:
                    skf = skf.replace(" & ()", "")
                if "() & " in skf:
                    skf = skf.replace("() & ", "")
                skfs.append(skf)

        return np.array(skfs)

    def get_skolem_function_cnf_2(self, args, gcln, no_of_input_var, input_var_idx, num_of_outputs, output_var_idx, io_dict, outidx):
        '''
        Reads the model weights (layer_or_weights, layer_and_weights) and builds the skolem function based on it.
        Input: Learned model parameters
        Output: Skolem Functions
        '''

        layer_or_weights_1 = gcln.cnf_layer_1.layer_or_weights.cpu(
        ).detach().numpy()  # input_size x K
        layer_and_weights_1 = gcln.cnf_layer_1.layer_and_weights.cpu(
        ).detach().numpy()  # K x num_of_outputs

        weights = [[layer_or_weights_1, layer_and_weights_1]]

        threshold = args.threshold
        K = args.K
        architecture = args.architecture
        hidden_size = gcln.cnf_layer_1.hidden_size

        literals = []
        neg_literals = []
        for i in input_var_idx:
            literals.append(io_dict.get(i))
            neg_literals.append("~"+io_dict.get(i))
            # literals.append("i"+str(i))
            # neg_literals.append("~i"+str(i))

        clause = np.array(literals + neg_literals)

        temp_dict = {}
        for i in range(args.layers):
            clause = self.read_cnf(threshold, architecture, weights[i][0],
                                   weights[i][1], hidden_size, num_of_outputs, K, clause)
            no_of_temp_vars = clause.shape[0]
            temp_var_name = "temp_"+str(i)+"_"+str(outidx)+"_"
            cl = []
            for j in range(no_of_temp_vars):
                temp = temp_var_name + str(j)
                cl.append(temp)
                if clause[j] == "(())" or clause[j] == "()":
                    temp_dict[temp] = "(one)"
                else:
                    temp_dict[temp] = clause[j]
            clause = np.array(cl)
        skfs = clause

        return skfs, temp_dict

    def read_dnf(self, threshold, architecture, layer_or_weights, layer_and_weights, hidden_size, num_of_outputs, K, clause):
        clauses = []
        if architecture == 1:
            for j in range(K):
                mask = layer_and_weights[:, j] > threshold
                clauses.append(list(clause[mask]))
            clauses = np.array(clauses, dtype=list)
        elif architecture == 2:
            for j in range(K):
                mask = layer_and_weights[:, j] > threshold
                clauses.append(list(clause[mask]))
            clauses = np.array(clauses, dtype=list)
        elif architecture == 3:
            for j in range(num_of_outputs * K):
                mask = layer_and_weights[:, j] > threshold
                clauses.append(list(clause[mask]))
            clauses = np.array(clauses, dtype=list)

        ored_clauses = []
        for j in range(len(clauses)):
            ored_clauses.append("("+" & ".join(clauses[j])+")")
        ored_clauses = np.array(ored_clauses)

        gated_ored_clauses = []
        if architecture == 1:
            mask = layer_or_weights > threshold
            ored_clause = ored_clauses.reshape((-1, 1))
            gated_ored_clauses.append(
                np.unique(ored_clause[mask]))

            skfs = []
            # for i in range(num_of_outputs):
            skf = " | ".join(gated_ored_clauses[0])  # +"\n"
            if " | ()" in skf:
                skf = skf.replace(" | ()", "")
            if "() | " in skf:
                skf = skf.replace("() | ", "")
            skfs.append(skf)

        elif architecture == 2:
            for i in range(num_of_outputs):
                mask = layer_or_weights[:, i] > threshold
                ored_clause = ored_clauses.reshape((-1, 1))
                gated_ored_clauses.append(
                    np.unique(ored_clause[mask]))

            skfs = []
            for i in range(num_of_outputs):
                skf = " | ".join(gated_ored_clauses[i])  # +"\n"
                if " | ()" in skf:
                    skf = skf.replace(" | ()", "")
                if "() | " in skf:
                    skf = skf.replace("() | ", "")
                skfs.append(skf)

        elif architecture == 3:
            for i in range(num_of_outputs):
                mask = layer_or_weights[i*K:(i+1)*K, :] > threshold
                ored_clause = ored_clauses.reshape((-1, 1))[i*K:(i+1)*K, :]
                gated_ored_clauses.append(
                    np.unique(ored_clause[mask]))

            skfs = []
            for i in range(num_of_outputs):
                skf = " | ".join(gated_ored_clauses[i])  # +"\n"
                if " | ()" in skf:
                    skf = skf.replace(" | ()", "")
                if "() | " in skf:
                    skf = skf.replace("() | ", "")
                skfs.append(skf)
        return np.array(skfs)

    def get_skolem_function_dnf(self, args, gcln, no_of_input_var, input_var_idx, num_of_outputs, output_var_idx, io_dict, outidx):
        '''
        Reads the model weights (layer_or_weights, layer_and_weights) and builds the skolem function based on it.
        Input: Learned model parameters
        Output: Skolem Functions
        '''

        layer_or_weights_1 = gcln.cnf_layer_1.layer_or_weights.cpu(
        ).detach().numpy()  # input_size x K
        layer_and_weights_1 = gcln.cnf_layer_1.layer_and_weights.cpu(
        ).detach().numpy()  # K x num_of_outputs

        weights = [[layer_or_weights_1, layer_and_weights_1]]

        threshold = args.threshold
        K = args.K
        architecture = args.architecture
        hidden_size = gcln.cnf_layer_1.hidden_size

        literals = []
        neg_literals = []
        for i in input_var_idx:
            literals.append(io_dict.get(i))
            neg_literals.append("~"+io_dict.get(i))
            # literals.append("i"+str(i))
            # neg_literals.append("~i"+str(i))

        clause = np.array(literals + neg_literals)

        temp_dict = {}
        for i in range(args.layers):
            clause = self.read_dnf(threshold, architecture, weights[i][0],
                                   weights[i][1], hidden_size, num_of_outputs, K, clause)
            no_of_temp_vars = clause.shape[0]
            temp_var_name = "temp_"+str(i)+"_"+str(outidx)+"_"
            cl = []
            for j in range(no_of_temp_vars):
                temp = temp_var_name + str(j)
                cl.append(temp)
                if clause[j] == "(())" or clause[j] == "()" or clause[j] == "":
                    temp_dict[temp] = "(one)"
                else:
                    temp_dict[temp] = clause[j]
            clause = np.array(cl)
        skfs = clause

        return skfs, temp_dict

    def dataLoader(self, training_samples, input_var_idx, output_var_idx, batch_size):
        # Define training data loader
        inps = training_samples[:, input_var_idx]
        tgts = training_samples[:, output_var_idx]
        dataset = TensorDataset(inps, tgts)
        train_loader = DataLoader(
            dataset, batch_size=batch_size, shuffle=False)
        return train_loader

    # MANTHAN MODULES FOR VERILOG INPUT FILES:

    def prepare_file_names(self, verilog_spec, verilog_spec_location):
        '''
        Returns path to verilog .v and varstoelim .txt files
        '''

        filename = verilog_spec.split(".v")[0]+"_varstoelim.txt"
        varlistfile = "benchmarks/" +\
            verilog_spec_location+"/Yvarlist/"+filename
        verilog = "benchmarks/" +\
            verilog_spec_location+"/"+verilog_spec

        return verilog, varlistfile

    def get_output_varlist(self, varlistfile):
        '''
        Reads output variables from varstoelim.txt
        Returns output variable list
        '''

        return [line.rstrip('\n')
                for line in open(varlistfile)]

    def get_temporary_variables(self, verilog, output_varlist):
        '''
        Creates temporary variables and returns them
        '''

        Xvar_tmp = []
        Yvar_tmp = []
        with open(verilog, 'r') as f:
            for x, line in enumerate(f):
                if line.startswith("module"):
                    line_split = line.split("(")
                    total_var = line_split[1].split(",")
                    for var in range(len(total_var) - 1):
                        variable_check = total_var[var]
                        variable_check = variable_check.strip(" ").strip("\n")
                        if str(variable_check) in output_varlist:
                            Yvar_tmp.append(var)
                        else:
                            Xvar_tmp.append(var)
        total_var = total_var[:-1]
        total_var = [e.strip() for e in total_var]
        return Xvar_tmp, Yvar_tmp, total_var

    def change_modulename(self, verilog):
        '''
        Changes module name in verilog file to FORMULA
        Returns modified verilog_formula
        '''

        verilog_formula = ''
        with open(verilog, 'r') as f:
            for x, line in enumerate(f):
                if line.startswith("module"):
                    modulename = line.split("(")[0].split(" ")[1]
                    line = line.replace(modulename, "FORMULA")
                verilog_formula += line

        return verilog_formula

    def preprocess_manthan(self, varlistfile, verilog, Xvar_tmp, Yvar_tmp):
        '''
        Preprocesses verilog files
        Returns variable information and unates
        '''

        inputfile_name = verilog.split(".v")[0]
        cmd = "./dependencies/preprocess -b %s -v %s > /dev/null 2>&1 " % (
            verilog, varlistfile)
        os.system(cmd)
        pos_unate = []
        neg_unate = []
        Xvar = []
        Yvar = []
        Xvar_map = []
        Yvar_map = []
        found_neg = 0
        exists = os.path.isfile(inputfile_name + "_vardetails")
        if exists:
            with open(inputfile_name + "_vardetails", 'r') as f:
                lines = f.readlines()
            f.close()
            for line in lines:
                if "Xvar " in line:
                    Xvar = line.split(":")[1].strip(" \n").split(" ")
                    Xvar = np.array(Xvar)
                    Xvar = Xvar.astype(int)
                    # first variable is 0 now, not 1
                    Xvar = np.subtract(Xvar, 1)
                    continue
                if "Yvar " in line:
                    Yvar = line.split(":")[1].strip(" \n").split(" ")
                    Yvar = np.array(Yvar)
                    Yvar = Yvar.astype(int)
                    # first variable is 0 now, not 1
                    Yvar = np.subtract(Yvar, 1)
                    continue
                if "Yvar_map " in line:
                    Yvar_map = line.split(":")[1].strip(" \n").split(" ")
                    Yvar_map = np.array(Yvar_map)
                    Yvar_map = Yvar_map.astype(int)
                    continue
                if "Xvar_map " in line:
                    Xvar_map = line.split(":")[1].strip(" \n").split(" ")
                    Xvar_map = np.array(Xvar_map)
                    Xvar_map = Xvar_map.astype(int)
                    continue
                if "Posunate" in line:
                    pos = line.split(":")[1].strip(" \n")
                    if pos != "":
                        pos_unate = pos.split(" ")
                        pos_unate = np.array(pos_unate)
                        pos_unate = pos_unate.astype(int)
                    continue
                if "Negunate" in line:
                    neg = line.split(":")[1].strip(" \n")
                    if neg != "":
                        neg_unate = neg.split(" ")
                        neg_unate = np.array(neg_unate)
                        neg_unate = neg_unate.astype(int)
                    continue
            os.unlink(inputfile_name + "_vardetails")
            Xvar_map = dict(zip(Xvar, Xvar_map))
            Yvar_map = dict(zip(Yvar, Yvar_map))
            Xvar = sorted(Xvar)
            Yvar = sorted(Yvar)
        else:
            print("preprocessing error .. continuing ")
            cmd = "./dependencies/file_generation_cnf %s %s.cnf %s_mapping.txt  > /dev/null 2>&1" % (
                verilog, inputfile_name, inputfile_name)
            os.system(cmd)
            print("cmd: ", cmd)
            with open(inputfile_name + "_mapping.txt", 'r') as f:
                lines = f.readlines()
            f.close()
            for line in lines:
                allvar_map = line.strip(" \n").split(" ")
            # print("allvars: ", allvar_map)
            os.unlink(inputfile_name + "_mapping.txt")
            allvar_map = np.array(allvar_map).astype(int)
            Xvar_map = dict(zip(Xvar_tmp, allvar_map[Xvar]))
            Yvar_map = dict(zip(Yvar_tmp, allvar_map[Yvar]))
            Xvar = np.sort(np.array(Xvar_tmp))
            Yvar = np.sort(np.array(Yvar_tmp))

        pos_unate_list = []
        neg_unate_list = []
        for unate in pos_unate:
            pos_unate_list.append(list(Yvar_map.keys())[
                                  list(Yvar_map.values()).index(unate)])
        for unate in neg_unate:
            neg_unate_list.append(list(Yvar_map.keys())[
                                  list(Yvar_map.values()).index(unate)])

        return pos_unate_list, neg_unate_list, Xvar, Yvar, Xvar_map, Yvar_map

    def preprocess_wrapper(self, verilog_spec, verilog_spec_location):
        '''
        Preprocesses verilog input file and finds unates
        Input: verilog input file
        Output: variable information and unates
        '''

        verilog, varlistfile = self.prepare_file_names(
            verilog_spec, verilog_spec_location)
        output_varlist = self.get_output_varlist(
            varlistfile)  # Y variable list
        # output_varlist = ["i"+e.split("_")[1]
        #                   for e in output_varlist if "_" in e]
        output_varlist = ["i"+e[1:].replace("_", "")
                          for e in output_varlist]
        Xvar_tmp, Yvar_tmp, total_vars = self.get_temporary_variables(
            verilog, output_varlist)
        total_varsz3 = [e.replace("_", "") for e in total_vars]
        # total_vars = ["i"+e.split("_")[1] for e in total_vars if "_" in e]
        total_vars = ["i"+e[1:].replace("_", "") for e in total_vars]
        verilog_formula = self.change_modulename(verilog)
        pos_unate, neg_unate, Xvar, Yvar, Xvar_map, Yvar_map = self.preprocess_manthan(
            varlistfile, verilog, Xvar_tmp, Yvar_tmp
        )
        return verilog, output_varlist, total_vars, total_varsz3, verilog_formula, pos_unate, neg_unate, Xvar, Yvar, Xvar_map, Yvar_map

    def unate_skolemfunction(self, Xvar, Yvar, pos_unate, neg_unate, inputfile_name):

        skolemformula = tempfile.gettempdir() + \
            '/' + inputfile_name + \
            "_skolem.v"  # F(X,Y')
        inputstr = 'module SKOLEMFORMULA ('
        declarestr = ''
        assignstr = ''
        itr = 1
        for var in range(len(Xvar) + len(Yvar)):
            inputstr += "i%s, " % (var)
            if var in Xvar:
                declarestr += "input i%s;\n" % (var)
            if var in Yvar:
                declarestr += "output i%s;\n" % (var)
                if var in neg_unate:
                    assignstr += "assign i%s = 0;\n" % (var)
                if var in pos_unate:
                    assignstr += "assign i%s = 1;\n" % (var)
        inputstr += ");\n"
        f = open(skolemformula, "w")
        f.write(inputstr)
        f.write(declarestr)
        f.write(assignstr)
        f.write("endmodule")
        f.close()
        cmd = "./dependencies/file_write_verilog %s %s > /dev/null 2>&1  " % (
            skolemformula, skolemformula)
        os.system(cmd)

    def check_unates(self, pos_unate, neg_unate, Xvar, Yvar, inputfile_name):
        # if all Y variables are unate
        if len(pos_unate) + len(neg_unate) == len(Yvar):
            print(len(pos_unate) + len(neg_unate))
            print("positive unate", len(pos_unate))
            print("all Y variables are unates")
            print("Solved !! done !")
            self.unate_skolemfunction(
                Xvar, Yvar, pos_unate, neg_unate, inputfile_name)
            skolemformula = tempfile.gettempdir() + \
                '/' + inputfile_name + "_skolem.v"
            exists = os.path.isfile(skolemformula)
            # if exists:
            #     os.system("cp " + skolemformula +
            #             " ./skfs/" + inputfile_name + "_skolem.v")
            exists = os.path.isfile("strash.txt")
            if exists:
                os.unlink("strash.txt")
            exists = os.path.isfile("variable_mapping.txt")
            if exists:
                os.unlink("variable_mapping.txt")
            return True

    def prepare_cnf_content(self, verilog, Xvar, Yvar, Xvar_map, Yvar_map, pos_unate, neg_unate):

        cnffile = verilog.split(".v")[0] + ".cnf"
        # print("prep cnf: ", Yvar, Yvar_map)

        # to add c ind and positive and negative unate in cnf
        unates = []
        indIter = 1
        indStr = 'c ind '
        allvar_map = []
        for i in range(len(Xvar) + len(Yvar)):
            if i in Xvar:
                i_map = Xvar_map[i]
            if i in Yvar:
                i_map = Yvar_map[i]
            allvar_map.append(i_map)
            if indIter % 10 == 0:
                indStr += ' 0\nc ind '
            indStr += "%d " % i_map
            indIter += 1
        indStr += " 0\n"
        allvar_map = np.array(allvar_map)
        fixedvar = ''
        for i in pos_unate:
            fixedvar += "%s 0\n" % (Yvar_map[i])
            unates.append(i)
        for i in neg_unate:
            fixedvar += "-%s 0\n" % (Yvar_map[i])
            unates.append(i)
        with open(cnffile, 'r') as f:
            lines = f.readlines()
        f.close()
        fixedvar += "%s 0\n" % (1)  # output variable always true.

        unates = np.sort(unates)
        cnf_content = ''
        for line in lines:
            line = line.strip(" \n")
            if line.startswith("c"):
                continue
            if line.startswith('p cnf'):
                numVar = int(line.split()[2])
                numCls = int(line.split()[3])
                line = line.replace("p cnf " + str(numVar) + " " + str(
                    numCls), "p cnf " + str(numVar) + " " + str(numCls + len(unates) + 1))
            cnf_content += line + "\n"
        cnf_content = cnf_content.strip("\n")
        cnf_content = indStr + cnf_content + "\n" + fixedvar.rstrip(' \n')
        os.unlink(cnffile)

        return cnf_content, allvar_map

    def get_sample_cms(self, allvar_map, cnf_content, no_samples, verilog):
        weighted = 1
        seed = 10
        verbose = 0
        inputfile_name = verilog.split("/")[-1][:-2]

        tempcnffile = tempfile.gettempdir() + '/' + inputfile_name + ".cnf"
        f = open(tempcnffile, "w")
        f.write(cnf_content)
        f.close()
        tempoutputfile = tempfile.gettempdir() + '/' + inputfile_name + "_.txt"
        if weighted:
            cmd = "./dependencies/cryptominisat5 -n1 --sls 0 --comps 0"
            cmd += " --restart luby  --nobansol --maple 0 --presimp 0"
            cmd += " --polar weight --freq 0.9999 --verb 0 --scc 0"
            cmd += " --random %s --maxsol %s" % (seed, no_samples)
            cmd += " %s" % (tempcnffile)
            cmd += " --dumpresult %s > /dev/null 2>&1" % (tempoutputfile)
        else:
            cmd = "./dependencies/cryptominisat5 --restart luby"
            cmd += " --maple 0 --verb 0 --nobansol"
            cmd += " --scc 1 -n1 --presimp 0 --polar rnd --freq 0.9999"
            cmd += " --random %s --maxsol %s" % (seed, no_samples)
            cmd += " %s" % (tempcnffile)
            cmd += " --dumpresult %s > /dev/null 2>&1" % (tempoutputfile)
        if verbose:
            print("cmd: ", cmd)
        os.system(cmd)
        with open(tempoutputfile, 'r') as f:
            content = f.read()
        f.close()
        os.unlink(tempoutputfile)
        os.unlink(tempcnffile)
        content = content.replace("SAT\n", "").replace(
            "\n", " ").strip(" \n").strip(" ")
        models = content.split(" ")
        models = np.array(models)
        if(models[len(models) - 1] != '0'):
            models = np.delete(models, len(models) - 1, axis=0)
        index = np.where(models == "0")[0][0]
        var_model = np.reshape(models, (-1, index + 1)).astype(int)
        one = np.ones(len(allvar_map), dtype=int)
        allvar_map = np.subtract(allvar_map, one).astype(int)
        var_model = var_model[:, allvar_map]
        var_model = var_model > 1
        var_model = var_model.astype(int)
        return var_model

    def adaptive_samples(self, sample_cnf_content, Yvar_map, allvar_map, verilog):
        sample_cnf_content_one = ''
        sample_cnf_content_zero = ''
        bias = {}
        for var in Yvar_map.keys():
            sample_cnf_content_one += "w %d 0.9\n" % (Yvar_map[var])
            sample_cnf_content_zero += "w %d 0.1\n" % (Yvar_map[var])
        samples_one = self.get_sample_cms(
            allvar_map, sample_cnf_content + sample_cnf_content_one, 500, verilog)
        samples_zero = self.get_sample_cms(
            allvar_map, sample_cnf_content + sample_cnf_content_zero, 500, verilog)
        for var in Yvar_map.keys():
            len_one = np.count_nonzero(samples_one[:, var])
            p = round(float(len_one) / 500, 2)
            len_zero = np.count_nonzero(samples_zero[:, var])
            q = round(float(len_zero) / 500, 3)
            if 0.35 < p < 0.65 and 0.35 < q < 0.65:
                bias[var] = p
            else:
                bias[var] = 0.9
        return bias

    def gen_weighted_cnf(self, cnf_content, Xvar_map, Yvar_map, allvar_map, verilog):
        adaptivesample = 1
        lines = cnf_content.split("\n")
        sample_cnf_content = ''
        for line in lines:
            line = line.strip("\n")
            if line == '':
                continue
            if line.startswith("c"):
                sample_cnf_content += line + "\n"
                continue
            if line.startswith('p cnf'):
                numVar = int(line.split()[2])
                numCls = int(line.split()[3])
                line = line.replace("p cnf " + str(numVar) + " " + str(numCls), "p cnf " + str(
                    numVar) + " " + str(numCls + len(Xvar_map.keys()) + len(Yvar_map.keys())))
                sample_cnf_content += line + "\n"
                continue
            sample_cnf_content += line + "\n"
        for var in Xvar_map.keys():
            sample_cnf_content += "w %d 0.5\n" % (Xvar_map[var])
        if adaptivesample:
            bias_y = self.adaptive_samples(
                sample_cnf_content, Yvar_map, allvar_map, verilog)
            for var in Yvar_map.keys():
                sample_cnf_content += "w %d %f\n" % (
                    Yvar_map[var], bias_y[var])
        else:
            for var in Yvar_map.keys():
                sample_cnf_content += "w %d 0.9\n" % (Yvar_map[var])
        return sample_cnf_content

    def generate_samples(self, cnf_content, Xvar, Yvar, Xvar_map, Yvar_map, allvar_map, verilog, max_samples=1000):

        SAMPLER_CMS = 1
        samples = 1
        weighted = 1
        if SAMPLER_CMS:
            sample_cnf_content = cnf_content
            if samples:
                no_samples = max_samples
            else:
                if(len(Yvar) + len(Xvar) < 1200):
                    no_samples = 10000
                if ((len(Yvar) + len(Xvar) > 1200) and (len(Yvar) + len(Xvar) < 4000)):
                    no_samples = 5000
                if(len(Yvar) + len(Xvar) > 4000):
                    no_samples = 1000

            if weighted:
                sample_cnf_content = self.gen_weighted_cnf(
                    cnf_content, Xvar_map, Yvar_map, allvar_map, verilog)
            samples = self.get_sample_cms(
                allvar_map, sample_cnf_content, no_samples, verilog)
        # x_data, indices = np.unique(
        #     samples[:, Xvar], axis=0, return_index=True)
        # samples = samples[indices, :]
        samples = np.unique(samples, axis=0)

        # x_data, indices = np.unique(samples[:, Xvar], axis=0, return_index=True)
        # samples = samples[indices, :]

        return samples

    def get_var_counts(self, Xvar, Yvar, verilog):
        num_of_vars = len(Xvar) + len(Yvar)
        num_out_vars = len(Yvar)
        f = open(verilog, 'r')
        data = f.read()
        num_of_eqns = data.count('assign')
        f.close()

        return num_of_vars, num_out_vars, num_of_eqns

    def prepare_candidateskf(self, skfunc, Yvar, pos_unate, neg_unate):
        candidateskf = {}
        j = 0
        for i in Yvar:
            # if i in neg_unate:
            #     candidateskf[i] = ' 0 '
            #     continue
            # if i in pos_unate:
            #     candidateskf[i] = ' 1 '
            #     continue
            if j < len(skfunc):
                candidateskf[i] = skfunc[j]
            j += 1

        return candidateskf

    def create_skolem_function(self, inputfile_name, candidateskf, temp_content, Xvar, Yvar, total_varsz3):
        # we have candidate skolem functions for every y in Y
        # Now, lets generate Skolem formula F(X,Y') : input X and output Y'
        tempOutputFile = tempfile.gettempdir() + \
            '/' + inputfile_name + \
            "_skolem.v"  # F(X,Y')

        inputstr = 'module SKOLEMFORMULA ('
        declarestr = ''
        assignstr = ''
        wirestr = 'wire zero;\nwire one;\n'
        wirestr += "assign zero = 0;\nassign one = 1;\n"
        outstr = ''
        itr = 1
        wtlist = []
        for var in range(len(Xvar) + len(Yvar)):
            inputstr += "%s, " % (total_varsz3[var])
            if var in Xvar:
                declarestr += "input %s;\n" % (total_varsz3[var])
            if var in Yvar:
                flag = 0
                declarestr += "input %s;\n" % (total_varsz3[var])
                wirestr += "wire w%s;\n" % (total_varsz3[var])
                assignstr += 'assign w%s = (' % (total_varsz3[var])
                if var in candidateskf:
                    temp = candidateskf[var].replace(
                        " 1 ", " one ").replace(" 0 ", " zero ")
                assignstr += temp + ");\n"
                outstr += "(~(w%s ^ %s)) & " % (
                    total_varsz3[var], total_varsz3[var])
                if itr % 10 == 0:
                    flag = 1
                    outstr = outstr.strip("& ")
                    wirestr += "wire wt%s;\n" % (itr)
                    assignstr += "assign wt%s = %s;\n" % (itr, outstr)
                    wtlist.append(itr)
                    outstr = ''

                itr += 1
        if(flag == 0):
            outstr = outstr.strip("& ")
            wirestr += "wire wt%s;\n" % (itr)
            assignstr += "assign wt%s = %s;\n" % (itr, outstr)
            wtlist.append(itr)
        assignstr += "assign out = "
        for i in wtlist:
            assignstr += "wt%s & " % (i)
        assignstr = assignstr.strip("& ") + ";\n"
        inputstr += " out );\n"
        declarestr += "output out ;\n"
        f = open(tempOutputFile, "w")
        f.write(inputstr)
        f.write(declarestr)
        f.write(wirestr)
        f.write(temp_content)
        f.write(assignstr)
        f.write("endmodule")
        f.close()

    def create_error_formula(self, Xvar, Yvar, verilog_formula):
        refine_var_log = {}

        inputformula = '('
        inputskolem = '('
        inputerrorx = 'module MAIN ('
        inputerrory = ''
        inputerroryp = ''
        declarex = ''
        declarey = ''
        declareyp = ''
        for var in range(len(Xvar) + len(Yvar)):
            if var in Xvar:
                inputformula += "i%s, " % (var)
                inputskolem += "i%s, " % (var)
                inputerrorx += "i%s, " % (var)
                declarex += "input i%s ;\n" % (var)
            if var in Yvar:
                refine_var_log[var] = 0
                inputformula += "i%s, " % (var)
                inputskolem += "ip%s, " % (var)
                inputerrory += "i%s, " % (var)
                inputerroryp += "ip%s, " % (var)
                declarey += "input i%s ;\n" % (var)
                declareyp += "input ip%s ;\n" % (var)
        inputformula += "out1 );\n"
        inputformula_sk = inputskolem + "out3 );\n"
        inputskolem += "out2 );\n"

        inputerrorx = inputerrorx + inputerrory + inputerroryp + "out );\n"
        declare = declarex + declarey + declareyp + 'output out;\n' + \
            "wire out1;\n" + "wire out2;\n" + "wire out3;\n"
        formula_call = "FORMULA F1 " + inputformula
        skolem_call = "SKOLEMFORMULA F2 " + inputskolem
        formulask_call = "FORMULA F2 " + inputformula_sk
        error_content = inputerrorx + declare + \
            formula_call + skolem_call + formulask_call
        error_content += "assign out = ( out1 & out2 & ~(out3) );\n" + \
            "endmodule\n"
        error_content += verilog_formula
        return error_content, refine_var_log

    def add_skolem_to_errorformula(self, error_content, selfsub, verilog):

        inputfile_name = verilog.split("/")[-1][:-2]
        skolemformula = tempfile.gettempdir() + '/' + inputfile_name + "_skolem.v"
        with open(skolemformula, 'r') as f:
            skolemcontent = f.read()
        f.close()
        errorformula = tempfile.gettempdir() + '/' + inputfile_name + "_errorformula.v"
        skolemcontent_write = ''
        if len(selfsub) != 0:
            for all_selfsub_var in selfsub:
                file_open = open(
                    tempfile.gettempdir()+"/selfsub/formula%s_true.v" % (all_selfsub_var), "r")
                content = file_open.read()
                file_open.close()
                skolemcontent_write += "\n" + content
        f = open(errorformula, "w")
        f.write(error_content)
        f.write(skolemcontent)
        f.write(skolemcontent_write)
        f.close()

    def createSkolem(self, candidateSkf, Xvar, Yvar, UniqueVars, UniqueDef, inputfile_name):
        tempOutputFile = tempfile.gettempdir() + '/' + inputfile_name + \
            "_skolem.v"  # F(X,Y')
        inputstr = 'module SKOLEMFORMULA ('
        declarestr = ''
        assignstr = ''
        wirestr = 'wire zero;\nwire one;\n'
        wirestr += "assign zero = 0;\nassign one = 1;\n"
        outstr = ''
        itr = 1
        wtlist = []

        for var in Xvar:
            declarestr += "input i%s;\n" % (var)
            inputstr += "i%s, " % (var)
        for var in Yvar:
            flag = 0
            declarestr += "input o%s;\n" % (var)
            inputstr += "o%s, " % (var)
            wirestr += "wire w%s;\n" % (var)
            if var not in UniqueVars:
                assignstr += 'assign w%s = (' % (var)
                assignstr += candidateSkf[var].replace(
                    " 1 ", " one ").replace(" 0 ", " zero ") + ");\n"

            outstr += "(~(w%s ^ o%s)) & " % (var, var)
            if itr % 10 == 0:
                flag = 1
                outstr = outstr.strip("& ")
                wirestr += "wire wt%s;\n" % (itr)
                assignstr += "assign wt%s = %s;\n" % (itr, outstr)
                wtlist.append(itr)
                outstr = ''
            itr += 1
        if(flag == 0):
            outstr = outstr.strip("& ")
            wirestr += "wire wt%s;\n" % (itr)
            assignstr += "assign wt%s = %s;\n" % (itr, outstr)
            wtlist.append(itr)
        assignstr += "assign out = "
        for i in wtlist:
            assignstr += "wt%s & " % (i)
        assignstr = assignstr.strip("& ") + ";\n"
        inputstr += " out );\n"
        declarestr += "output out ;\n"
        f = open(tempOutputFile, "w")
        f.write(inputstr + declarestr + wirestr)
        # f.write(UniqueDef.strip("\n")+"\n")
        f.write(assignstr + "endmodule")
        f.close()

    def createErrorFormula(self, Xvar, Yvar, UniqueVars, verilog_formula):
        inputformula = '('
        inputskolem = '('
        inputerrorx = 'module MAIN ('
        inputerrory = ''
        inputerroryp = ''
        declarex = ''
        declarey = ''
        declareyp = ''
        for var in Xvar:
            inputformula += "%s, " % (var)
            inputskolem += "%s, " % (var)
            inputerrorx += "%s, " % (var)
            declarex += "input %s ;\n" % (var)
        for var in Yvar:
            inputformula += "%s, " % (var)
            inputerrory += "%s, " % (var)
            declarey += "input %s ;\n" % (var)
            inputerroryp += "ip%s, " % (var)
            declareyp += "input ip%s ;\n" % (var)
            if var in UniqueVars:
                inputskolem += "%s, " % (var)
            else:
                inputskolem += "ip%s, " % (var)
        inputformula += "out1 );\n"
        inputformula_sk = inputskolem + "out3 );\n"
        inputskolem += "out2 );\n"
        inputerrorx = inputerrorx + inputerrory + inputerroryp + "out );\n"
        declare = declarex + declarey + declareyp + 'output out;\n' + \
            "wire out1;\n" + "wire out2;\n" + "wire out3;\n"
        formula_call = "FORMULA F1 " + inputformula
        skolem_call = "SKOLEMFORMULA F2 " + inputskolem
        formulask_call = "FORMULA F2 " + inputformula_sk
        error_content = inputerrorx + declare + \
            formula_call + skolem_call + formulask_call
        error_content += "assign out = ( out1 & out2 & ~(out3) );\n" + \
            "endmodule\n"
        error_content += verilog_formula
        return error_content

    def write_error_formula1(self, inputfile_name, verilog, verilog_formula, skfunc, temp_dict, Xvar, Yvar, total_varsz3, pos_unate, neg_unate):

        var_def = ""
        assigns = ""
        for i, (k, v) in enumerate(temp_dict.items()):
            var_def += "wire " + k + ";\n"
            assigns += "assign " + k + " = " + v + ";\n"
        temp_content = var_def + assigns

        candidateskf = self.prepare_candidateskf(
            skfunc, Yvar, pos_unate, neg_unate)
        self.create_skolem_function(
            inputfile_name, candidateskf, temp_content, Xvar, Yvar, total_varsz3)
        # self.createSkolem(candidateskf, Xvar, Yvar, [], [], inputfile_name)
        error_content, refine_var_log = self.create_error_formula(
            Xvar, Yvar, verilog_formula)
        # error_content = self.createErrorFormula(Xvar, Yvar, [], verilog_formula)
        self.add_skolem_to_errorformula(error_content, [], verilog)

    def write_error_formula2(self, inputfile_name, verilog, verilog_formula, skfunc, Xvar, Yvar, pos_unate, neg_unate):
        candidateskf = self.prepare_candidateskf(
            skfunc, Yvar, pos_unate, neg_unate)
        # self.create_skolem_function(
        #     inputfile_name, candidateskf, Xvar, Yvar)
        self.createSkolem(candidateskf, Xvar, Yvar, [], [], inputfile_name)
        # error_content, refine_var_log = self.create_error_formula(
        #     Xvar, Yvar, verilog_formula)
        error_content = self.createErrorFormula(
            Xvar, Yvar, [], verilog_formula)
        self.add_skolem_to_errorformula(error_content, [], verilog)

    def verify(self, Xvar, Yvar, verilog):
        inputfile_name = verilog.split("/")[-1][:-2]
        errorformula = tempfile.gettempdir() + '/' + inputfile_name + "_errorformula.v"
        cexfile = tempfile.gettempdir() + '/' + inputfile_name + "_cex.txt"
        f = tempfile.gettempdir()+'/'+"hello.txt"

        e = os.path.isfile("strash.txt")
        if e:
            os.system("rm strash.txt")
        cmd = "./dependencies/file_generation_cex %s %s > /dev/null 2>&1 " % (
            errorformula, cexfile)
        os.system(cmd)
        e = os.path.isfile("strash.txt")
        if e:
            os.system("rm strash.txt")
            exists = os.path.isfile(cexfile)
            if exists:
                ret = 1
                with open(cexfile, 'r') as f:
                    lines = f.readlines()
                f.close()
                os.unlink(cexfile)
                for line in lines:
                    model = line.strip(" \n")
                cex = list(map(int, model))
                templist = np.split(cex, [len(Xvar), len(Xvar) + len(Yvar)])
                modelx = templist[0]
                modely = templist[1]
                modelyp = templist[2]
                assert(len(modelx) == len(Xvar))
                assert(len(modelyp) == len(Yvar))
                assert(len(modely) == len(Yvar))
                model_cex = cexmodels(modelx, modely, modelyp)
                return(1, model_cex, ret)
            else:
                return(1, [], 0)
        else:
            return(0, [0], 1)

    #!/usr/bin/env python
    # -*- coding: utf-8 -*-
    '''
    Copyright (C) 2021 Priyanka Golia, Subhajit Roy, and Kuldeep Meel

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in
    all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
    THE SOFTWARE.
    '''

    def parse(self, inputfile):
        with open(inputfile) as f:
            lines = f.readlines()
        f.close()

        Xvar = []
        Yvar = []

        qdimacs_list = []
        for line in lines:
            if line.startswith("c"):
                continue
            if (line == "") or (line == "\n"):
                continue
            if line.startswith("p"):
                continue
            if line.startswith("a"):
                Xvar += line.strip("a").strip("\n").strip(" ").split(" ")[:-1]
                continue
            if line.startswith("e"):
                Yvar += line.strip("e").strip("\n").strip(" ").split(" ")[:-1]
                continue
            clause = line.strip(" ").strip("\n").strip(" ").split(" ")[:-1]

            if len(clause) > 0:
                clause = list(map(int, list(clause)))
                # print("clause: ", clause)
                # clause = [i-1 for i in clause if i>0]
                # for i in range(len(clause)):
                # 	if clause[i] < 0:
                # 		clause[i] = clause[i] + 1
                # 	elif clause[i] > 0:
                # 		clause[i] = clause[i] - 1

                # print("clause: ", clause)
                # clause = [i+1 for i in clause if i<0]
                # qdimacs_list.append(clause)
        print("len qdimacs list: ", len(qdimacs_list))
        if (len(Xvar) == 0) or (len(Yvar) == 0) or (len(qdimacs_list) == 0):
            print("problem with the files, can not synthesis Skolem functions")

        Xvar = list(map(int, list(Xvar)))
        # Xvar = [i-1 for i in Xvar]
        Yvar = list(map(int, list(Yvar)))
        # Yvar = [i-1 for i in Yvar]

        return Xvar, Yvar, qdimacs_list

    def convertcnf(self, inputfile, cnffile_name):
        with open(inputfile, "r") as f:
            cnfcontent = f.read()
        f.close()

        cnfcontent = cnfcontent.replace("a ", "c ret ")
        cnfcontent = cnfcontent.replace("e ", "c ind ")

        with open(cnffile_name, "w") as f:
            f.write(cnfcontent)
        f.close()
        return cnfcontent

    def preprocess(self, cnffile_name):

        cmd = "./dependencies/preprocess2 %s " % (cnffile_name)
        with Popen(cmd, shell=True, stdout=PIPE, preexec_fn=os.setsid) as process:
            try:
                output = process.communicate(timeout=500)[0]
            except Exception:
                os.killpg(process.pid, signal.SIGINT)
                PosUnate = []
                NegUnate = []
                print("timeout preprocessing..")
                return PosUnate, NegUnate
            else:
                PosUnate = []
                NegUnate = []
                exists = os.path.isfile(cnffile_name + "_vardetails")
                if exists:
                    with open(cnffile_name + "_vardetails", 'r') as f:
                        lines = f.readlines()
                    f.close()

                    for line in lines:
                        if "Posunate" in line:
                            pos = line.split(":")[1].strip(" \n")
                            if pos != "":
                                PosUnate = list(map(int, list(pos.split(" "))))
                            continue
                        if "Negunate" in line:
                            neg = line.split(":")[1].strip(" \n")
                            if neg != "":
                                NegUnate = list(map(int, list(neg.split(" "))))
                            continue
                    os.unlink(cnffile_name + "_vardetails")
                else:
                    print("preprocessing error .. contining ")
                    exit()
                return PosUnate, NegUnate

    # generate samples manthan 2
    def computeBias(self, Xvar, Yvar, sampling_cnf, sampling_weights_y_1, sampling_weights_y_0, inputfile_name, SkolemKnown, args):
        samples_biased_one = self.generatesample(
            args, 500, sampling_cnf + sampling_weights_y_1, inputfile_name, 1)
        samples_biased_zero = self.generatesample(
            args, 500, sampling_cnf + sampling_weights_y_0, inputfile_name, 1)

        bias = ""

        for yvar in Yvar:
            if yvar in SkolemKnown:
                continue
            count_one = count_nonzero(samples_biased_one[:, yvar-1])
            p = round(float(count_one)/500, 2)

            count_zero = count_nonzero(samples_biased_zero[:, yvar-1])
            q = round(float(count_zero)/500, 2)

            if 0.35 < p < 0.65 and 0.35 < q < 0.65:
                bias += "w %s %s\n" % (yvar, p)
            elif q <= 0.35:
                if float(q) == 0.0:
                    q = 0.001
                bias += "w %s %s\n" % (yvar, q)
            else:
                if float(p) == 1.0:
                    p = 0.99
                bias += "w %s %s\n" % (yvar, p)

        return sampling_cnf + bias

    def generatesample(self, args, num_samples, sampling_cnf, inputfile_name, weighted):
        tempcnffile = tempfile.gettempdir() + '/' + inputfile_name + "_sample.cnf"
        with open(tempcnffile, "w") as f:
            f.write(sampling_cnf)
        f.close()

        tempoutputfile = tempfile.gettempdir() + '/' + inputfile_name + "_.txt"
        seed = 10
        if weighted:
            cmd = "./dependencies/cryptominisat5 -n1 --sls 0 --comps 0"
            cmd += " --restart luby  --nobansol --maple 0 --presimp 0"
            cmd += " --polar weight --freq 0.9999 --verb 0 --scc 0"
            cmd += " --random %s --maxsol %s > /dev/null 2>&1" % (
                seed, int(num_samples))
            cmd += " %s" % (tempcnffile)
            cmd += " --dumpresult %s " % (tempoutputfile)
        else:
            cmd = "./dependencies/cryptominisat5 --restart luby"
            cmd += " --maple 0 --verb 0 --nobansol"
            cmd += " --scc 1 -n1 --presimp 0 --polar rnd --freq 0.9999"
            cmd += " --random %s --maxsol %s" % (seed, int(num_samples))
            cmd += " %s" % (tempcnffile)
            cmd += " --dumpresult %s > /dev/null 2>&1" % (tempoutputfile)

        os.system(cmd)

        with open(tempoutputfile, "r") as f:
            content = f.read()
        f.close()
        os.unlink(tempoutputfile)
        os.unlink(tempcnffile)
        content = content.replace("SAT\n", "").replace(
            "\n", " ").strip(" \n").strip(" ")
        models = content.split(" ")
        models = np.array(models)
        if models[len(models)-1] != "0":
            models = np.delete(models, len(models) - 1, axis=0)
        if len(np.where(models == "0")[0]) > 0:
            index = np.where(models == "0")[0][0]
            var_model = np.reshape(models, (-1, index+1)).astype(np.int)
            var_model = var_model > 0
            var_model = np.delete(var_model, index, axis=1)
            var_model = var_model.astype(np.int)
        return var_model


# Init utilities
util = utils()
