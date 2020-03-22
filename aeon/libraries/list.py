from .helper import aefunction
'''
@aetype("type List<T>", lambda x: x)
class List(object):
    def __init__(self, next):
        self.next = next

def empty_list():
    return List(None)

def cons(list):
    return

'''


@aetype("""type List<T> {
    size : Integer;
}""")
class List(object):
    def __init__(self, next):
        self.next = next


@aetype('empty_list<T> : () -> { l:List<T> | l.size == 0} = native;')
def empty_list(ignored):
    return []
