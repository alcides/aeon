class Node(object):
    def __init__(self, nt, *children, **kwargs):
        self.nodet = nt
        self.nodes = children

        self.refined = None

        for k in kwargs:
            setattr(self, k, kwargs[k])

    def __str__(self):
        if hasattr(self, 'type'):
            return "§{}({}):{}".format(self.nodet, ", ".join([str(a) for a in self.nodes]), self.type)
        else:
            return "§{}({})".format(self.nodet, ", ".join([str(a) for a in self.nodes]))

    def __repr__(self):
        return str(self)

    def __getitem__(self, i):
        return self.nodes[i]
