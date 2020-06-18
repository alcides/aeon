import seaborn as sns
import matplotlib.pyplot as plt


def plot(path, f_name, axis, labels, data, order=None):
    try:
        plot_inner(path, f_name, axis, labels, data, order)
    except Exception as e:
        print("Exception plotting", f_name, e)


def plot_inner(path, f_name, axis, labels, data, order=None):

    print('Generating violinplot:', f_name)

    y, x = axis
    ylabel, xlabel = labels
    if labels[1] == 'Semantic Diversity':
        # Initialize figure and ax
        fig, ax = plt.subplots()

        # Set the scale of the x-and y-axes
        ax.set(xscale="log")

    sns.set(style='whitegrid', palette='muted')

    plot = sns.violinplot(x=x,
                          y=y,
                          data=data,
                          inner='stick',
                          orient='h',
                          order=order)
    plot.set(xlabel=xlabel, ylabel=ylabel)
    plot.xaxis.set_major_locator(plt.MaxNLocator(integer=True))

    ma = data[x].max()
    plot.set_xlim(left=0, right=ma + 0.5)

    f_name = '{}violin_{}.pdf'.format(path, f_name.replace(" ", "_"))

    figure = plot.get_figure()
    figure.savefig(f_name, bbox_inches='tight')
    figure.clf()
