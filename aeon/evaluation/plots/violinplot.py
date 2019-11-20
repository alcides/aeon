import seaborn as sns


def plot(path, f_name, axis, labels, data):

    print('Generating violinplot:', f_name)

    x, y = axis
    xlabel, ylabel = labels

    sns.set(style='whitegrid', palette='muted')

    plot = sns.violinplot(x=x, y=y, data=data, inner='points')
    plot.set(xlabel=xlabel, ylabel=ylabel)

    f_name = '{}violin_{}.pdf'.format(path, f_name)

    figure = plot.get_figure()
    figure.savefig(f_name)
    figure.clf()
