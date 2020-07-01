from .annotation import aefunction, aedocumentation

''' Pair binds in Aeon to Python '''

@aefunction("""type Pair[T1, T2] {
    elem1 : T1;
    elem2 : T2;
}""", None)
class Pair(object):
    def __init__(self):
        pass

# Creates a pair
@aefunction('create_pair[T1, T2](e1 : T1, e2 : T2) -> {p:Pair | e1 == p.e1 && e2 == p.e2} = native;', lambda e1: lambda e2: create_pair(e1, e2))
def create_pair(e1, e2):
    return (e1, e2)

@aefunction('pair_first[T1, T2](p : Pair[T1, T2]) -> {e1:T1 | e1 == p.e1} = native;', lambda p: pair_first(p))
def pair_first(pair):
    return pair[0]

@aefunction('pair_second[T1, T2](p : Pair[T1, T2]) -> {e2:T2 | e2 == p.e2} = native;', lambda p: pair_second(p))
def pair_second(pair):
    return pair[1]
