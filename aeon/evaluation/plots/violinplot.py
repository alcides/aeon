import seaborn as sns
import matplotlib.pyplot as plt


def plot(path, f_name, axis, labels, data):

    print('Generating violinplot:', f_name)

    y, x = axis
    ylabel, xlabel = labels

    sns.set(style='whitegrid', palette='muted')

    plot = sns.violinplot(x=x, y=y, data=data, inner='points', orient='h')
    plot.set(xlabel=xlabel, ylabel=ylabel)
    plot.yaxis.set_major_locator(plt.MaxNLocator(integer=True))

    f_name = '{}violin_{}.pdf'.format(path, f_name)

    figure = plot.get_figure()
    figure.savefig(f_name)
    figure.clf()
