import seaborn as sns 
import matplotlib.pyplot as plt

def plot(path, f_name, axis, labels, data):

    print('Generating scatterplot:', f_name)

    x, y = axis
    xlabel, ylabel = labels

    sns.set(style='whitegrid', palette='muted')

    plot = sns.swarmplot(x=x, y=y, data=data)
    plot.set(xlabel=xlabel, ylabel=ylabel)

    plot.yaxis.set_major_locator(plt.MaxNLocator(integer=True))
    f_name = '{}scatter_{}.pdf'.format(path, f_name)

    figure = plot.get_figure()
    figure.savefig(f_name)
    figure.clf()
