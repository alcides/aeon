from aeon.frontend_core import typee, TypingContext
from aeon.synthesis.synthesis import se
from aeon.typechecker.typing import check_type

ty = typee.parse

def setUp():
    ctx = TypingContext()
    ctx.setup()
    return ctx

def provide(*args, **kwargs):
    def wrapper(function):
        
        passed = 0

        # SetUp the refined input generator
        context = setUp()
        typees = [ty(param) for param in args]
        repeat = 1 if 'repeat' not in kwargs else kwargs['repeat']

        for _ in range(repeat):
            values = [se(context, T, 0).value for T in typees]
            try:
                function(*values)
                print("SUCCESS: Refined test passed for input values: {}".format(values))
                passed += 1
            except AssertionError as err:
                print("ERROR: Refined test failed for input values: {}".format(values))
        
        print()
        print("-"*80)
        print("Report:")
        print("Tests failed: {} / {}".format(repeat - passed, repeat))
        return function
    return wrapper