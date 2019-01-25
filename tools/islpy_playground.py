from islpy import *

"""
Example of isl performing Refined Type Checking

ex:

create(n:Integer) -> _:Array<type=T,size=n> where { 0 <= n }
get(arr:Array<type=T, size=n>, i:Integer) -> r:T where { 0 <= i < n }
plus(int k) -> m:Integer where { m = k + 1 }


let b = random_int()
let a = create(10)
let b = 10
print(get(a, b))
let c = plus(b)
print(get(a, c))
"""

type_of = {
    'create': {
        'pre': [
            Set("[create_def_n] -> { : 0 <= create_def_n }")
        ],
        'pos': [
            Set("[create_def_n, create_def_return_n] -> { : create_def_n = create_def_return_n }")
        ]
    },
    'get':  {
        'pre': [
            Set("[get_def_arr_n, get_def_i] -> { : 0 <= get_def_i < get_def_arr_n }")
        ],
        'pos': []
    },
    'plus': {
        'pre': [],
        'pos': [
               Set("[plus_def_i, plus_return_n] -> { : plus_def_i + 1 = plus_return_n }")
        ]
    }
}

def merge_sets(l):
    u = Set("{ : }")
    for e in l:
        u = u.intersect(e)
    return u


def set_filter_vars(set, names):
    if not names:
        return Set.universe(Space.alloc(DEFAULT_CONTEXT, 0, 0, 0))
    return set.project_out_except(names, [1 for i in names])

def set_replace_vars(set, replacements = {}):
    """
        replaments is a dict with { old->new }
    """
    for k in replacements:
        other_set = Set("[{0}, {1}] -> {{ : {0} = {1} }}".format(k, replacements[k]))
        set = set.intersect(other_set)
    return set_filter_vars(set, replacements.values())

def typecheck_invocation(fname, args):
    dtypes = type_of[fname]
    pre_conditions = merge_sets(dtypes['pre'])
    pos_conditions = merge_sets(dtypes['pos'])
    appl = pre_conditions
    assert(not appl.is_empty())
    for cond in args:
        t = appl.intersect(cond)
        if t.is_empty():
            raise Error("Type checking failed at {} when merging {} with {}".format(fname, appl, cond))
        else:
            appl = t
    appl = appl.intersect(pos_conditions)
    #print dir(appl)
    #print appl.split_dims.__doc__

    ps = [ pos_conditions.get_dim_name(1,i) for i in range(pos_conditions.dim(1)) if 'return' in pos_conditions.get_dim_name(1,i) ]
    return set_filter_vars(appl, ps)

try:
    _t = typecheck_invocation("create", [ Set("[create_def_n] -> { : create_def_n=-1 }") ])
    assert(False)
except:
    pass # expected

"""let a = create(10)"""

t_lit_10 = Set("[integer_lit_10] -> { : integer_lit_10=10 }")
t_inv_create = typecheck_invocation("create", [ set_replace_vars(t_lit_10, {'integer_lit_10': 'create_def_n'}) ])
t_a = set_replace_vars(t_inv_create, { 'create_def_return_n':'array_a_n' })

""" let b = 9 """

t_b = Set("[integer_b] -> { : integer_b=9 }")

""" print(get(a, b)) """


t_inv_get = typecheck_invocation("get", [
    set_replace_vars(t_a, {'array_a_n': 'get_def_arr_n'}),
    set_replace_vars(t_b, {'integer_b': 'get_def_i'}),
])
assert(t_inv_get.complement().is_empty())


""" let c = plus(b) """

t_inv_plus = typecheck_invocation("plus", [
    set_replace_vars(t_b, {'integer_b': 'plus_def_i'}),
])
t_c = set_replace_vars(t_inv_plus, {'plus_return_n': 'integer_c'})

""" get(a, c) """

#t_inv_get = typecheck_invocation("get", [
#    set_replace_vars(t_a, {'array_a_n': 'get_def_arr_n'}),
#    set_replace_vars(t_c, {'integer_c': 'get_def_i'}),
#])
#assert(t_inv_get.complement().is_empty())

#def typecheck(i):
#    type_of["a"] = type_of['create_n'].intersect(Set("[n] -> { : n = 10 }"))
#    type_of['get_inv'] = type_of['get_i'].intersect(type_of['a'])
#    str_condition = "[i] -> {{: i = {}}}".format(i)
#    type_of['get_args'] = type_of['get_inv'].intersect(Set(str_condition))
#    return not type_of['get_args'].is_empty()
#print(typecheck(9))
#print(typecheck(10))


s1 = Set("[x] -> { : 10 < x <= 12 }")
s2 = Set("[x,y] -> { : x+y = 10 }")

print(s1.intersect(s2).complement())


s1 = Set("[x] -> { : }")
s2 = Set("[x] -> { : x > 3 }")

print s1.
