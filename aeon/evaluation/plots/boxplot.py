import seaborn as sns
import matplotlib.pyplot as plt

def reversed_plot(path, f_name, axis, labels, data):
    axis = axis[::-1]
    labels = axis
    orient = 'h'
    f_name = '{}_{}'.format(f_name, 'reversed')
    plot(path, f_name, axis, labels, data, orient)

def plot(path, f_name, axis, labels, data, orient='v'):
    
    print('Generating boxplot:', f_name)

    x, y = axis
    xlabel, ylabel = labels

    sns.set(style='ticks')

    f, ax = plt.subplots(figsize=(7, 6))
    f_name = '{}box_{}.pdf'.format(path, f_name)

    plot = sns.boxplot(x=x, 
                       y=y, 
                       data=data, 
                       whis='range', 
                       palette='vlag')
    plot.set(xlabel=xlabel, ylabel=ylabel)
    plot.yaxis.set_major_locator(plt.MaxNLocator(integer=True))

    figure = plot.get_figure()
    figure.savefig(f_name)
    figure.clf()
