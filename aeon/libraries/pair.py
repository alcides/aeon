from .annotation import aefunction, aedocumentation

''' Pair binds in Aeon to Python '''

@aefunction("""type Pair[X, Y] {
    elem1 : X;
    elem2 : Y;
}""")
class Pair(object):
    def __init__(self):
        pass

# Creates a pair
@aefunction('create_pair[X, Y](e1 : X, e2 : Y) -> {p:Pair[X, Y] | e1 == p.elem1 && e2 == p.elem2};')
def create_pair(e1, e2):
    return (e1, e2)

@aefunction('pair_first[X, Y](p : Pair[X, Y]) -> {e1:X | e1 == p.elem1};')
def pair_first(pair):
    return pair[0]

@aefunction('pair_second[X, Y](p : Pair[X, Y]) -> {e2:Y | e2 == p.elem2};')
def pair_second(pair):
    return pair[1]
