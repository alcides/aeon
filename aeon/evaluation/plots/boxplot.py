import seaborn as sns
import matplotlib.pyplot as plt

def plot(path, f_name, axis, labels, data, orient='v'):

    print('Generating boxplot:', f_name)

    y, x = axis
    ylabel, xlabel = labels

    sns.set(style='ticks')

    f_name = '{}box_{}.pdf'.format(path, f_name)

    plot = sns.boxplot(x=x, y=y, data=data, whis='range', palette='vlag', orient='h')
    plt.ylabel(ylabel, rotation = 0)
    plot.set(xlabel=xlabel)
    plot.xaxis.set_major_locator(plt.MaxNLocator(integer=True))

    figure = plot.get_figure()
    figure.savefig(f_name)
    figure.clf()
