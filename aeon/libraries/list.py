from .standard import aetype
'''
@aetype("type List<T>")
class List(object):
    def __init__(self, next):
        self.next = next
    
def empty_list():
    return List(None)

def cons(list):
    return 

'''


@aetype('type List;')
class List(object):
    def __init__(self, next):
        self.next = next


@aetype('empty_list : () -> l:List<T> /* where {l.size == 0} */ = native;')
def empty_list():
    return []
