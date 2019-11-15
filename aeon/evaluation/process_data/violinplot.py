import seaborn as sns

def plot(data):
    sns.set(style='whitegrid', palette='muted')
    
    plot = sns.violinplot(x=data.columns[0], y=data.columns[1], data=data, inner='points')

    figure = plot.get_figure()
    figure.savefig('graphics/violin_{}.png'.format(data.columns[1]))
    figure.clf()
