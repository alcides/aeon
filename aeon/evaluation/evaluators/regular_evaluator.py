import pandas as pd
from os import listdir

from .evaluator import Evaluator
from aeon.frontend2 import expr, typee

import aeon.evaluation.plots.boxplot as boxplot
import aeon.evaluation.plots.violinplot as violinplot
import aeon.evaluation.plots.scatterplot as scatterplot

ex = expr.parse_strict
ty = typee.parse_strict

class RegularEvaluator(Evaluator):

    # CONSTANTS
    PATH = 'regular/'

    def __init__(self):
        self.path = self.FOLDER_PATH + self.PATH
        self.typees = [ty('Integer'), 
                       ty('Double'),]
    
    def get_depth(self):
        return self.MAX_TREE_DEPTH

    def process(self):
        csv = [pd.read_csv(self.path + f) for f in listdir(self.path)]
        csv = self.metric_separation(csv)

        # Generate the plots
        for metric, data in csv.items():
            axis = ('Typee', metric)
            labels = axis
            f_name = metric
            scatterplot.plot(self.path, f_name, axis, labels, data)
            boxplot.plot(self.path, f_name, axis, labels, data)
            violinplot.plot(self.path, f_name, axis, labels, data)

    def metric_separation(self, data):
        result = {}
        for csv in data:
            typee_column = csv.columns[0]
            for column in csv.columns[2:]:
                new_data = csv[[typee_column, column]]
                if column not in result:
                    result[column] = new_data
                else:
                    result[column] = pd.concat([result[column], new_data])
        return result