from aeon.synthesis.inequalities import *
from aeon.libraries.stdlib import ty2

from aeon.synthesis.ranges import *
from aeon.types import TypingContext, t_i

from sympy import *
from sympy.solvers.inequalities import *

from aeon.translator import translate

from aeon.typechecker.typing import synth_type

name = 'x'

x = Symbol(name)
RangedContext.Variable = name

typees = [
    # Integer
    ty2('{x:Integer where (x >= 0) && (x <= 10)}'),
    ty2('{x:Integer where ((x >= 0) && (x <= 10)) && (x != 5)}'),
    ty2('{x:Integer where (x % 2) == 0}'),
    ty2('{x:Integer where !((x % 2) == 0)}'),
    ty2('{x:Integer where ((x % 2) == 0) --> (x > 0)}'),
    ty2('{x:Integer where (\y:Integer -> x > y)(10)}'),
    
    # Double
    ty2("{x:Double where !((x < 0.0) || (x > 10.0))}"),
    ty2("{x:Double where (x > 10.0) --> ((x >= 10.0) && (x <= 20.0))}"),

    # Boolean
    ty2('{x:Boolean where x == true}'),
    ty2('{x:Boolean where x || true}'),
    ty2('{x:Boolean where (x || true) --> x}'),

    # String
    ty2('{x:String where (_String_size(x)) == 0}'),
    ty2('{x:String where (_String_size(x)) > 0 && (_String_size(x)) < 10}'),
    ty2('{x:String where (_String_size(x)) % 2 == 0}'),

    #
    #ty2('Person'),
    #ty2('{p:Person where (_Person_age(p)) >= 18 --> (_Person_height(p)) > 120}'),
    #ty2('{p:Person where (_Person_size(_Person_name(p))) == 3 }'),    
]

# Set the contexts
ctx = TypingContext()
ctx.setup()


for T in typees:
    print()
    print("="*40)
    print("Generating expression for condition:", translate(T))

    ctx = ctx.with_var(name, T.type)
    ctx.restrictions = list() 
    ctx.restrictions.append(T.cond)


    # Annotate the types of the conditions
    T.cond.type = synth_type(ctx, T.cond)
    
    expression = Literal(ranged(ctx, T.type), T.type)

    print("Generated the expression:", expression)