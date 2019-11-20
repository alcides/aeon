import re
import pandas as pd
from os import listdir

from .evaluator import Evaluator
from aeon.evaluation import OUTPUT_PATH
from aeon.frontend2 import expr, typee

import aeon.evaluation.plots.boxplot as boxplot
import aeon.evaluation.plots.violinplot as violinplot
import aeon.evaluation.plots.scatterplot as scatterplot

class RegularEvaluator(Evaluator):

    # CONSTANTS
    PATH = 'regular/'

    def __init__(self):
        self.path = self.FOLDER_PATH + self.PATH

    def process(self):

        data = {}

        for f in listdir(OUTPUT_PATH):
            _, depth, _ = tuple(map(lambda x: int(x), re.findall('\d+', f)))
            csv = pd.read_csv(OUTPUT_PATH + f)
            data[depth] = csv if depth not in data else pd.concat([data[depth], csv])

        for depth, csv in data.items():
            
            result = self.treat_data(csv)

            # Generate the plots
            for metric, res in result.items():
                axis = ('Typee', metric)
                labels = axis
                f_name = 'depth{}_{}'.format(depth, metric)
                scatterplot.plot(self.path, f_name, axis, labels, res)
                boxplot.plot(self.path, f_name, axis, labels, res)
                violinplot.plot(self.path, f_name, axis, labels, res)

    def treat_data(self, data):
        result = {}
        typee_column = data.columns[0]
        for column in data.columns[2:]:
            new_data = data[[typee_column, column]]
            if column not in result:
                result[column] = new_data
            else:
                result[column] = pd.concat([result[column], new_data])
        return result