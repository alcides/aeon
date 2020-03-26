import re
import pandas as pd

from os import listdir

from .evaluator import Evaluator
from aeon.evaluation import OUTPUT_PATH
from aeon.frontend2 import expr, typee

import aeon.evaluation.plots.boxplot as boxplot
import aeon.evaluation.plots.violinplot as violinplot
import aeon.evaluation.plots.scatterplot as scatterplot


def rename(n):
    if n == 'Multiple of 4':
        return 'M4'
    if n == 'Smaller than 10 Natural':
        return 'Lt10'
    if n == 'Abstract Integer':
        return 'Abs'
    if n == 'Refined Abstract Integer':
        return 'AbsR'
    if n == 'Refined Input-Output':
        return 'RAbsR'
    if n == 'Refined Double Abstract Integer':
        return 'AbsAbs'
    return n


class RegularEvaluator(Evaluator):

    # CONSTANTS
    PATH = 'regular/'

    def __init__(self):
        self.path = self.FOLDER_PATH + self.PATH

    def process(self):

        data = {}

        for f in listdir(OUTPUT_PATH):
            if not f.endswith(".csv"):
                continue
            depth = int(
                re.search(r'\d+',
                          re.findall('depth\d+', f)[0]).group())
            csv = pd.read_csv(OUTPUT_PATH + f)
            data[depth] = csv if depth not in data else pd.concat(
                [data[depth], csv])

        for depth, csv in data.items():

            result = self.treat_data(csv)

            # Generate the plots
            for metric, res in result.items():
                res['Pretty Typee'] = res['Pretty Typee'].map(rename)
                if metric.endswith('Diversity'):
                    v = res[metric].count()
                    res[metric].map(lambda x: x / float(v))
                axis = ('Pretty Typee', metric)

                labelx = metric
                if metric == 'Diversity':
                    labelx = 'Syntactic Diversity'

                labels = ('Types', labelx)
                f_name = 'depth{}_{}'.format(depth, metric)

                order = [
                    'Integer', 'Natural', 'M4', 'Lt10', 'Boolean', 'String',
                    'Double', 'Abs', 'AbsR', 'RAbsR', 'AbsAbs'
                ]

                if metric == 'Tree Depth':
                    res2 = res.groupby([
                        'Pretty Typee', 'Tree Depth'
                    ]).size().reset_index(name='treedepthcount')
                    #print(res2)
                    scatterplot.plot(self.path,
                                     f_name + "_hist",
                                     axis,
                                     labels,
                                     res2,
                                     order=order,
                                     size='treedepthcount')
                scatterplot.plot(self.path,
                                 f_name,
                                 axis,
                                 labels,
                                 res,
                                 order=order)
                boxplot.plot(self.path, f_name, axis, labels, res, order=order)
                violinplot.plot(self.path,
                                f_name,
                                axis,
                                labels,
                                res,
                                order=order)

    def treat_data(self, data):
        result = {}
        typee_column = data.columns[1]
        for column in data.columns[3:]:
            new_data = data[[typee_column, column]]
            if column not in result:
                result[column] = new_data
            else:
                result[column] = pd.concat([result[column], new_data])
        return result
