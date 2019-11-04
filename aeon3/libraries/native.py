import builtins

def print(x):
    builtins.print('PRINT:', x)
    return x

def abs(value):
    return builtins.abs(value)

def id(value):
    return value

def forall(list, function):
    all(map(lambda x : function(x), lista))

def exists(list, function):
    any(map(lambda x : function(x), lista))

def fix(function):
    function(lambda x: fix(function)(x))

def match_csv(path):
    return "HELLO CSV!"
    #with open(path, 'r') as file:
    #    my_reader = csv.reader(file, delimiter=',')
    #    for row in my_reader:
    #        print(row)