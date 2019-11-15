import seaborn as sns
import matplotlib.pyplot as plt

def plot(data):
    sns.set(style='ticks')
    
    f, ax = plt.subplots(figsize=(7, 6))

    plot = sns.boxplot(x=data.columns[1], y=data.columns[0], data=data, whis='range', palette='vlag')

    figure = plot.get_figure()
    figure.savefig('graphics/box_{}.png'.format(data.columns[1]))
    figure.clf()
