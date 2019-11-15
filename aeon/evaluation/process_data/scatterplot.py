import seaborn as sns

def plot(data):
    sns.set(style='whitegrid', palette='muted')
    plot = sns.swarmplot(x='Typee', y=data.columns[1], data=data)

    figure = plot.get_figure()
    figure.savefig('graphics/scatter_{}.png'.format(data.columns[1]))
    figure.clf()
