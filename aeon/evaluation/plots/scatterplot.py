import seaborn as sns

def plot(path, f_name, axis, labels, data):

    x, y = axis
    xlabel, ylabel = labels

    sns.set(style='whitegrid', palette='muted')
    
    plot = sns.swarmplot(x=x, y=y, data=data)
    plot.set(xlabel=xlabel, ylabel=ylabel)

    f_name = '{}scatter_{}.svg'.format(path, f_name)

    figure = plot.get_figure()
    figure.savefig(f_name)
    figure.clf()
