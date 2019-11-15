import aeon.evaluation.process_data.boxplot as boxplot
import aeon.evaluation.process_data.violinplot as violinplot
import aeon.evaluation.process_data.scatterplot as scatterplot

import pandas as pd
from os import listdir

# Process the data in the path
def process(folder_path: str):
    csv = [pd.read_csv(folder_path + f) for f in listdir(folder_path)]
    csv = metric_separation(csv)

    # Generate the plots
    for metric, data in csv.items():
        scatterplot.plot(data)
        boxplot.plot(data)
        violinplot.plot(data)

def metric_separation(data):
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