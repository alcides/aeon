import seaborn as sns
import matplotlib.pyplot as plt


def plot(path,
         f_name,
         axis,
         labels,
         data,
         order=None,
         hue=None,
         split=False,
         size=None):

    print('Generating scatterplot:', f_name)

    y, x = axis
    ylabel, xlabel = labels
    if labels[1] == 'Semantic Diversity':
        # Initialize figure and ax
        fig, ax = plt.subplots()

        # Set the scale of the x-and y-axes
        ax.set(xscale="log")
    sns.set(style='whitegrid', palette='muted')
    if split:
        figure, (ax1, ax2) = plt.subplots(ncols=2, nrows=1, sharey=True)
        ax1.set_xlim(-2000, 2000)
        ax1.set(xscale="linear")
        ax2.set_xlim(3294966344, 5294966344)
        ax2.set(xscale="linear")
        ax2.get_yaxis().set_visible(False)

        v_order = ['default', 'qflra', 'qflra-history', 'aeon']

        data['Type'] = data['Typee']

        y = 'Type'

        plot1 = sns.catplot(x=x,
                            y=y,
                            data=data,
                            orient='h',
                            hue=hue,
                            dodge=True,
                            ax=ax1,
                            order=order,
                            legend=False,
                            hue_order=v_order)
        plot2 = sns.catplot(x=x,
                            y=y,
                            data=data,
                            orient='h',
                            hue=hue,
                            dodge=True,
                            ax=ax2,
                            order=order,
                            margin_titles=False,
                            hue_order=v_order)
        plot1.set(xlabel=xlabel, ylabel=ylabel)
        plot2.set(xlabel=xlabel, ylabel="")
        plt.ylabel("")
        ax1.legend().remove()
    else:
        #if size != None:
        #    plot = sns.scatterplot(x=x, y=y, data=data, hue=hue, order=order, size=size)
        #else:
        plot = sns.swarmplot(x=x,
                             y=y,
                             data=data,
                             orient='h',
                             hue=hue,
                             dodge=True,
                             order=order)
        plot.set(xlabel=xlabel, ylabel=ylabel)
        if labels[1] != 'Semantic Diversity':
            plot.xaxis.set_major_locator(plt.MaxNLocator(integer=True))
            plot.set_xlim(left=0)
        else:
            plot.set_xlim(left=0.7)
        figure = plot.get_figure()
    f_name = '{}scatter_{}.pdf'.format(path, f_name.replace(" ", "_"))

    figure.savefig(f_name, bbox_inches='tight')
    figure.clf()
