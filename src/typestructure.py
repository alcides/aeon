class Type(object):
    def __init__(self, type="Object", arguments=None, parameters=None, conditions=None, effects=None):
        self.type = type
        self.arguments = arguments
        self.parameters = parameters and parameters or []
        self.conditions = conditions and conditions or []
        self.effects = effects and effects or []

    def __str__(self):
        t = self.type
        if self.parameters:
            t += "<" + ", ".join(map(str, self.parameters)) + ">"
        if self.arguments:
            t = "({})".format(", ".join(map(str, self.arguments))) + " -> " + t
        # TODO DT and effects
        return t

    def __eq__(self, other):
        if type(other) != Type:
            return False
        # TODO DT and effects
        return self.type == other.type and \
            self.arguments == other.arguments and \
            len(self.parameters) == len(other.parameters)

# defaults
t_v = Type('Void')
t_n = Type('Object')
t_i = Type('Integer')
t_b = Type('Boolean')
t_f = Type('Float')
