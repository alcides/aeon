import re
import pandas as pd
import numpy as np

from os import listdir
from functools import reduce

from aeon.evaluation.evaluators.evaluator import Evaluator
from aeon.evaluation import OUTPUT_PATH

import aeon.evaluation.plots.boxplot as boxplot
import aeon.evaluation.plots.violinplot as violinplot
import aeon.evaluation.plots.scatterplot as scatterplot

class Z3Evaluator(Evaluator):

    # Constants
    PATH = 'z3/'

    def __init__(self):
        self.path = self.FOLDER_PATH + self.PATH

    def process(self):
        data = pd.DataFrame()
        path = 'aeon/evaluation/z3/'
        for f in listdir(path):
            if f.endswith('.csv'):
                csv = pd.read_csv(path + f)
                data = pd.concat([data, csv])

        result = self.treat_data(data)

        for metric, res in result.items():
            axis = ('Typee', metric)
            labels = ('Types', metric)
            f_name = '{}'.format(metric)
            res = res.sort_values(by=['Typee'])
            scatterplot.plot(path, f_name, axis, labels, res)
            boxplot.plot(path, f_name, axis, labels, res)
            violinplot.plot(path, f_name, axis, labels, res)


    def treat_data(self, data):
        result = {}
        typee_column = data.columns[0]
        for column in data.columns[1:]:
            new_data = data[[typee_column, column]]
            if column not in result:
                result[column] = new_data
            else:
                result[column] = pd.concat([result[column], new_data])
        return result