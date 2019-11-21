import seaborn as sns
import matplotlib.pyplot as plt


def plot(path, f_name, axis, labels, data):

    print('Generating scatterplot:', f_name)

    y, x = axis
    ylabel, xlabel = labels

    sns.set(style='whitegrid', palette='muted')

    plot = sns.swarmplot(x=x, y=y, data=data, orient='h')
    plot.set(xlabel=xlabel, ylabel=ylabel)
    plot.xaxis.set_major_locator(plt.MaxNLocator(integer=True))
    plot.set_xlim(left=0)
    f_name = '{}scatter_{}.pdf'.format(path, f_name)

    figure = plot.get_figure()
    figure.savefig(f_name, bbox_inches='tight')
    figure.clf()
