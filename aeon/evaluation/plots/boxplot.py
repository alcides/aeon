import seaborn as sns
import matplotlib.pyplot as plt

def plot(path, f_name, axis, labels, data):
    
    print('Generating boxplot:', f_name)

    x, y = axis
    xlabel, ylabel = labels

    sns.set(style='ticks')
    
    f, ax = plt.subplots(figsize=(7, 6))
    f_name = '{}box_{}.pdf'.format(path, f_name)

    plot = sns.boxplot(x=y, y=x, data=data, whis='range', palette='vlag', orient='h')
    plot.set(xlabel=ylabel, ylabel=xlabel)
    # plot = sns.boxplot(x=x, y=y, data=data, whis='range', palette='vlag')
    # plot.set(xlabel=xlabel, ylabel=ylabel)
    

    figure = plot.get_figure()
    figure.savefig(f_name)
    figure.clf()
