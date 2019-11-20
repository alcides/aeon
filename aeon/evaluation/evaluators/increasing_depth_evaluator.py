import re
import pandas as pd
from os import listdir

from .evaluator import Evaluator
from aeon.evaluation import OUTPUT_PATH
from aeon.frontend2 import expr, typee

import aeon.evaluation.plots.boxplot as boxplot
import aeon.evaluation.plots.violinplot as violinplot
import aeon.evaluation.plots.scatterplot as scatterplot


class IncreasingDepthEvaluator(Evaluator):

    # CONSTANTS
    PATH = 'increasing_depth/'

    def __init__(self):
        self.path = self.FOLDER_PATH + self.PATH

    def process(self):
        data = {}

        for f in listdir(OUTPUT_PATH):
            _, depth, _ = tuple(map(lambda x: int(x), re.findall('\d+', f)))
            csv = pd.read_csv(OUTPUT_PATH + f)
            data[depth] = csv if depth not in data else pd.concat(
                [data[depth], csv])

        df = pd.DataFrame()

        for max_depth, dataframe in data.items():
            df[str(max_depth + 1)] = pd.Series(dataframe['Tree Depth'].values)

        # Generate the plots
        axis = (None, None)
        labels = ('Maximum Depth', 'Depth')
        f_name = 'depth'

        #scatterplot.plot(self.path, f_name, axis, labels, df)
        boxplot.plot(self.path, f_name, axis, labels, df)
        violinplot.plot(self.path, f_name, axis, labels, df)
