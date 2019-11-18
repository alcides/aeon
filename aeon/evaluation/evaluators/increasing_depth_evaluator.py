import re
import pandas as pd
from os import listdir

from .evaluator import Evaluator
from aeon.frontend2 import expr, typee

import aeon.evaluation.plots.boxplot as boxplot
import aeon.evaluation.plots.violinplot as violinplot
import aeon.evaluation.plots.scatterplot as scatterplot

ex = expr.parse_strict
ty = typee.parse_strict

class IncreasingDepthEvaluator(Evaluator):

    # CONSTANTS
    PATH = 'increasing_depth/'

    def __init__(self):
        self.depth = 0
        self.path = self.FOLDER_PATH + self.PATH
        self.typees = [ty('Integer')] * self.MAX_TREE_DEPTH
    
    def get_depth(self):
        result = self.depth
        self.depth += 1
        return result

    def process(self):
        data = pd.DataFrame()

        for f in listdir(self.path):
            csv = pd.read_csv(self.path + f)['Tree Depth']
            name = str(int(re.findall('\d+', f)[0]) + 1)
            data[name] = csv

        # Generate the plots
        axis = (None, None)
        labels = ('Maximum Depth', 'Depth')
        f_name = 'depth'

        scatterplot.plot(self.path, f_name, axis, labels, data)
        boxplot.plot(self.path, f_name, axis, labels, data)
        violinplot.plot(self.path, f_name, axis, labels, data)
            