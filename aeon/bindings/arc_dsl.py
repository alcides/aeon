from typing import Union, Tuple, Any, Container, Callable, FrozenSet
from collections import Counter
import functools

Boolean = bool
Integer = int
IntegerTuple = Tuple[Integer, Integer]
Numerical = Union[Integer, IntegerTuple]
IntegerSet = FrozenSet[Integer]
Grid = Tuple[Tuple[Integer]]
Cell = Tuple[Integer, IntegerTuple]
Object = FrozenSet[Cell]
Objects = FrozenSet[Object]
Indices = FrozenSet[IntegerTuple]
IndicesSet = FrozenSet[Indices]
Patch = Union[Object, Indices]
Element = Union[Object, Grid]
Piece = Union[Grid, Patch]
TupleTuple = Tuple[Tuple]
ContainerContainer = Container[Container]


def identity(x: Any) -> Any:
    return x


def add(a: Numerical, b: Numerical) -> Numerical:
    try:
        if isinstance(a, int) and isinstance(b, int):
            return a + b
        a_t = a if isinstance(a, tuple) else (a, a)
        b_t = b if isinstance(b, tuple) else (b, b)
        return (a_t[0] + b_t[0], a_t[1] + b_t[1])
    except (TypeError, IndexError):
        return a  # Return one of the inputs as a fallback


def subtract(a: Numerical, b: Numerical) -> Numerical:
    try:
        if isinstance(a, int) and isinstance(b, int):
            return a - b
        a_t = a if isinstance(a, tuple) else (a, a)
        b_t = b if isinstance(b, tuple) else (b, b)
        return (a_t[0] - b_t[0], a_t[1] - b_t[1])
    except (TypeError, IndexError):
        return a


def multiply(a: Numerical, b: Numerical) -> Numerical:
    try:
        if isinstance(a, int) and isinstance(b, int):
            return a * b
        a_t = a if isinstance(a, tuple) else (a, a)
        b_t = b if isinstance(b, tuple) else (b, b)
        return (a_t[0] * b_t[0], a_t[1] * b_t[1])
    except (TypeError, IndexError):
        return a


def divide(a: Numerical, b: Numerical) -> Numerical:
    try:
        if isinstance(b, int):
            if b == 0:
                return a  # Avoid division by zero
            if isinstance(a, int):
                return a // b
            return (a[0] // b, a[1] // b)

        # b is a tuple
        b0, b1 = b
        if b0 == 0 and b1 == 0:
            return a  # Avoid division by zero

        if isinstance(a, int):
            x = a // b0 if b0 != 0 else a
            y = a // b1 if b1 != 0 else a
            return (x, y)

        # a is a tuple
        x = a[0] // b0 if b0 != 0 else a[0]
        y = a[1] // b1 if b1 != 0 else a[1]
        return (x, y)
    except (TypeError, IndexError):
        return a


def invert(n: Numerical) -> Numerical:
    try:
        return -n if isinstance(n, int) else (-n[0], -n[1])
    except (TypeError, IndexError):
        return n


def even(n: Integer) -> Boolean:
    return n % 2 == 0


def double(n: Numerical) -> Numerical:
    return multiply(n, 2)


def halve(n: Numerical) -> Numerical:
    return divide(n, 2)


def flip(b: Boolean) -> Boolean:
    return not b


def equality(a: Any, b: Any) -> Boolean:
    return a == b


def contained(value: Any, container: Container) -> Boolean:
    """element of"""
    try:
        return value in container
    except TypeError:
        # container is not a valid container type
        return False


def combine(a: Container, b: Container) -> Container:
    """union"""
    try:
        return type(a)((*a, *b))
    except TypeError:
        if hasattr(a, "union"):
            try:
                # Make elements of b hashable before the union
                hashable_b = frozenset(make_hashable(item) for item in b)
                return a.union(hashable_b)
            except TypeError:  # If b itself isn't iterable
                return a
        return a


def intersection(a: FrozenSet, b: FrozenSet) -> FrozenSet:
    """returns the intersection of two containers"""
    return a & b


def difference(a: FrozenSet, b: FrozenSet) -> FrozenSet:
    """set difference"""
    return a - b


def dedupe(tup: Tuple) -> Tuple:
    """remove duplicates"""
    if not isinstance(tup, tuple):
        return tuple()
    try:
        hashable_tup = tuple(make_hashable(item) for item in tup)
        return tuple(dict.fromkeys(hashable_tup).keys())
    except TypeError:
        # Fallback in case make_hashable fails for some reason
        return tup


def order(container: Container, compfunc: Callable) -> Tuple:
    """order container by custom key"""
    try:
        return tuple(sorted(list(container), key=compfunc))
    except (TypeError, ValueError):
        # Fallback if compfunc cannot be applied to the items
        return tuple(container)


def repeat(item: Any, num: Integer) -> Tuple:
    """repetition of item within vector"""
    # Clamp num to a reasonable range to avoid memory errors
    safe_num = max(0, min(num, 100))
    return tuple(item for _ in range(safe_num))


def greater(a: Integer, b: Integer) -> Boolean:
    """greater"""
    return a > b


def size(container: Container) -> Integer:
    """cardinality"""
    try:
        return len(container)
    except TypeError:
        return 0


def merge(containers: Container[Container[Any]]) -> Container:
    """merging"""
    if not containers:
        return tuple()
    first_elem = next(iter(containers), None)
    if not isinstance(first_elem, (list, tuple, set, frozenset)):
        return containers
    try:
        inner_type = type(first_elem)
        return inner_type(e for c in containers for e in c)
    except Exception:
        return frozenset(
            make_hashable(e) for c in containers if hasattr(c, "__iter__") and not isinstance(c, str) for e in c
        )


def maximum(container: IntegerSet) -> Integer:
    """maximum"""
    # Filter for integers only to prevent TypeError with mixed types
    int_only = [i for i in container if isinstance(i, int)]
    return max(int_only, default=0)


def minimum(container: IntegerSet) -> Integer:
    """minimum"""
    # Filter for integers only to prevent TypeError with mixed types
    int_only = [i for i in container if isinstance(i, int)]
    return min(int_only, default=0)


def valmax(container: Container, compfunc: Callable) -> Integer:
    """maximum by custom function"""
    if not container:
        return 0

    values = []
    for item in container:
        try:
            values.append(compfunc(item))
        except (TypeError, ValueError):
            continue  # Skip items that cause an error

    return max(values, default=0)


def valmin(container: Container, compfunc: Callable) -> Integer:
    """minimum by custom function"""
    if not container:
        return 0

    values = []
    for item in container:
        try:
            values.append(compfunc(item))
        except (TypeError, ValueError):
            continue  # Skip items that cause an error

    return min(values, default=0)


def argmax(container: Container, compfunc: Callable) -> Any:
    """largest item by custom order"""
    if not container:
        return None
    try:
        return max(container, key=compfunc)
    except (TypeError, ValueError):
        # Fallback if compfunc fails
        return next(iter(container), None)


def argmin(container: Container, compfunc: Callable) -> Any:
    """smallest item by custom order"""
    if not container:
        return None
    try:
        return min(container, key=compfunc)
    except (TypeError, ValueError):
        # Fallback if compfunc fails
        return next(iter(container), None)


def mostcommon(container: Container) -> Any:
    """most common item"""
    if not container:
        return None
    try:
        hashable_items = [make_hashable(item) for item in container]
        return Counter(hashable_items).most_common(1)[0][0]
    except (TypeError, IndexError):
        return next(iter(container), None)


def leastcommon(container: Container) -> Any:
    """least common item"""
    if not container:
        return None
    try:
        hashable_items = [make_hashable(item) for item in container]
        return Counter(hashable_items).most_common()[-1][0]
    except (TypeError, IndexError):
        return next(iter(container), None)


def make_hashable(value: Any) -> Any:
    """Recursively converts unhashable collections to their hashable counterparts."""
    if isinstance(value, list):
        return tuple(make_hashable(v) for v in value)
    if isinstance(value, set):
        return frozenset(make_hashable(v) for v in value)
    if isinstance(value, dict):
        return frozenset((k, make_hashable(v)) for k, v in value.items())
    return value


def initset(value: Any) -> FrozenSet:
    """initialize container"""
    try:
        hashable_value = make_hashable(value)
        return frozenset({hashable_value})
    except TypeError:
        # Fallback for truly unhashable types
        return frozenset()


def both(a: Boolean, b: Boolean) -> Boolean:
    """logical and"""
    return a and b


def either(a: Boolean, b: Boolean) -> Boolean:
    """logical or"""
    return a or b


def increment(x: Numerical) -> Numerical:
    """incrementing"""
    return add(x, 1)


def decrement(x: Numerical) -> Numerical:
    """decrementing"""
    return subtract(x, 1)


def crement(x: Numerical) -> Numerical:
    """incrementing positive and decrementing negative"""
    try:
        if isinstance(x, int):
            return 0 if x == 0 else (x + 1 if x > 0 else x - 1)
        return (
            0 if x[0] == 0 else (x[0] + 1 if x[0] > 0 else x[0] - 1),
            0 if x[1] == 0 else (x[1] + 1 if x[1] > 0 else x[1] - 1),
        )
    except (TypeError, IndexError):
        return x


def sign(x: Numerical) -> Numerical:
    """sign"""
    try:
        if isinstance(x, int):
            return 0 if x == 0 else (1 if x > 0 else -1)
        return (0 if x[0] == 0 else (1 if x[0] > 0 else -1), 0 if x[1] == 0 else (1 if x[1] > 0 else -1))
    except (TypeError, IndexError):
        return x


def positive(x: Integer) -> Boolean:
    """positive"""
    return isinstance(x, int) and x > 0


def toivec(i: Integer) -> IntegerTuple:
    """vector pointing vertically"""
    return (i, 0) if isinstance(i, int) else (0, 0)


def tojvec(j: Integer) -> IntegerTuple:
    """vector pointing horizontally"""
    return (0, j) if isinstance(j, int) else (0, 0)


def sfilter(container: Container, condition: Callable) -> Container:
    """keep elements in container that satisfy condition"""
    try:
        return type(container)(e for e in container if condition(e))
    except (TypeError, ValueError):
        # Fallback if condition fails or container type can't be reconstructed
        return container


def mfilter(container: Container, function: Callable) -> FrozenSet:
    """filter and merge"""
    return merge(sfilter(container, function))


def extract(container: Container, condition: Callable) -> Any:
    """first element of container that satisfies condition"""
    try:
        return next(e for e in container if condition(e))
    except (StopIteration, TypeError, ValueError):
        # Fallback if no item matches or condition fails
        return next(iter(container), None)


def totuple(container: FrozenSet) -> Tuple:
    """conversion to tuple"""
    return tuple(container)


def first(container: Container) -> Any:
    """first item of container"""
    return next(iter(container), None)


def last(container: Container) -> Any:
    """last item of container"""
    try:
        # This works for sequences and can be a fallback for iterables
        c_list = list(container)
        return c_list[-1] if c_list else None
    except TypeError:
        return None


def insert(value: Any, container: FrozenSet) -> FrozenSet:
    """insert item into container"""
    try:
        hashable_value = make_hashable(value)
        return container.union({hashable_value})
    except TypeError:
        return container


def remove(value: Any, container: Container) -> Container:
    """remove item from container"""
    try:
        if isinstance(container, (list, tuple)):
            return type(container)(e for e in container if e != value)
        if isinstance(container, set):
            return container - {value}
    except TypeError:
        pass
    return container


def other(container: Container, value: Any) -> Any:
    """other value in the container"""
    if not hasattr(container, "__len__") or len(container) != 2:
        return None
    return first(remove(value, container))


def interval(start: Integer, stop: Integer, step: Integer) -> Tuple:
    """range"""
    if not all(isinstance(i, int) for i in [start, stop, step]):
        return tuple()
    if step == 0:
        step = 1
    # Clamp values to prevent excessive memory usage
    safe_start = max(-100, min(start, 100))
    safe_stop = max(-100, min(stop, 100))
    return tuple(range(safe_start, safe_stop, step))


def astuple(a: Integer, b: Integer) -> IntegerTuple:
    """constructs a tuple"""
    if not isinstance(a, int) or not isinstance(b, int):
        return (0, 0)
    return (a, b)


def product(a: Container, b: Container) -> FrozenSet:
    """cartesian product"""
    try:
        return frozenset((i, j) for j in b for i in a)
    except TypeError:
        return frozenset()


def pair(a: Tuple, b: Tuple) -> TupleTuple:
    """zipping of two tuples"""
    if not isinstance(a, tuple) or not isinstance(b, tuple):
        return tuple()
    return tuple(zip(a, b))


def branch(condition: Boolean, a: Any, b: Any) -> Any:
    """if else branching"""
    return a if condition else b


def compose(outer: Callable, inner: Callable) -> Callable:
    """function composition"""
    return lambda x: outer(inner(x))


def chain(h: Callable, g: Callable, f: Callable) -> Callable:
    """function composition with three functions"""
    return lambda x: h(g(f(x)))


def matcher(function: Callable, target: Any) -> Callable:
    """construction of equality function"""

    def robust_matcher(x):
        try:
            return equality(function(x), target)
        except Exception:
            return False

    return robust_matcher


def rbind(function: Callable, fixed: Any) -> Callable:
    """fix the rightmost argument"""
    return functools.partial(function, fixed)


def lbind(function: Callable, fixed: Any) -> Callable:
    """fix the leftmost argument"""
    return lambda *args: function(fixed, *args)


def power(function: Callable, n: Integer) -> Callable:
    """power of function"""
    safe_n = max(0, min(n, 10))  # Prevent deep recursion

    def powered_func(x):
        res = x
        for _ in range(safe_n):
            res = function(res)
        return res

    return powered_func


def fork(outer: Callable, a: Callable, b: Callable) -> Callable:
    """creates a wrapper function"""
    return lambda x: outer(a(x), b(x))


def apply(function: Callable, container: Container) -> Container:
    """apply function to each item in container"""
    if not callable(function):
        return container

    results = []
    if not hasattr(container, "__iter__"):
        return tuple()

    for e in container:
        try:
            results.append(function(e))
        except Exception:
            results.append(e)  # Keep original element if function fails
            continue
    try:
        return type(container)(results)
    except TypeError:
        return tuple(results)


def rapply(functions: Container, value: Any) -> Container:
    """apply each function in container to value"""
    results = []
    if not hasattr(functions, "__iter__"):
        return tuple()

    for f in functions:
        if callable(f):
            try:
                results.append(f(value))
            except Exception:
                # Function failed to execute, skip it
                continue
    try:
        return type(functions)(results)
    except TypeError:
        return tuple(results)


def mapply(function: Callable, container: Container[Container[Any]]) -> FrozenSet:
    """apply and merge"""
    return merge(apply(function, container))


def papply(function: Callable, a: Tuple, b: Tuple) -> Tuple:
    """apply function on two vectors"""
    return tuple(function(i, j) for i, j in zip(a, b))


def mpapply(function: Callable, a: Tuple, b: Tuple) -> Tuple:
    """apply function on two vectors and merge"""
    return merge(papply(function, a, b))


def prapply(function: Callable, a: Container, b: Container) -> FrozenSet:
    """apply function on cartesian product"""
    try:
        return frozenset(function(i, j) for j in b for i in a)
    except (TypeError, ValueError):
        return frozenset()


def mostcolor(element: Element) -> Integer:
    """most common color"""
    if not element:
        return 0
    try:
        values = [v for r in element for v in r] if isinstance(element, tuple) else [v for v, _ in element]
        if not values:
            return 0
        return Counter(values).most_common(1)[0][0]
    except (TypeError, IndexError, ValueError):
        return 0


def leastcolor(element: Element) -> Integer:
    """least common color"""
    if not element:
        return 0
    try:
        values = [v for r in element for v in r] if isinstance(element, tuple) else [v for v, _ in element]
        if not values:
            return 0
        return Counter(values).most_common()[-1][0]
    except (TypeError, IndexError, ValueError):
        return 0


def height(piece: Piece) -> Integer:
    """height of grid or patch"""
    try:
        if isinstance(piece, tuple):
            return len(piece)
        if not piece:
            return 0
        return lowermost(piece) - uppermost(piece) + 1
    except TypeError:
        return 0


def width(piece: Piece) -> Integer:
    """width of grid or patch"""
    try:
        if isinstance(piece, tuple):
            return len(piece[0]) if piece else 0
        if not piece:
            return 0
        return rightmost(piece) - leftmost(piece) + 1
    except (TypeError, IndexError):
        return 0


def shape(piece: Piece) -> IntegerTuple:
    """height and width of grid or patch"""
    return (height(piece), width(piece))


def portrait(piece: Piece) -> Boolean:
    """whether height is greater than width"""
    h, w = shape(piece)
    return h > w


def colorcount(element: Element, value: Integer) -> Integer:
    """number of cells with color"""
    try:
        if isinstance(element, tuple):
            return sum(row.count(value) for row in element)
        return sum(v == value for v, _ in element)
    except TypeError:
        return 0


def colorfilter(objs: Objects, value: Integer) -> Objects:
    """filter objects by color"""
    if not isinstance(objs, frozenset):
        return frozenset()
    filtered = set()
    for obj in objs:
        try:
            if next(iter(obj))[0] == value:
                filtered.add(obj)
        except (TypeError, IndexError, StopIteration):
            continue
    return frozenset(filtered)


def toindices(patch: Patch) -> Indices:
    """indices of object cells"""
    if not patch or not isinstance(patch, (set, frozenset)):
        return frozenset()
    try:
        first_item = next(iter(patch))
        # Check if the patch is an Object (set of (color, index))
        if isinstance(first_item, tuple) and len(first_item) == 2 and isinstance(first_item[1], tuple):
            return frozenset(index for value, index in patch)
        # Assume it's already a set of indices
        return patch
    except (TypeError, IndexError, StopIteration):
        return frozenset()


def uppermost(patch: Patch) -> Integer:
    """row index of uppermost occupied cell"""
    indices = toindices(patch)
    return min((i for i, j in indices), default=0)


def lowermost(patch: Patch) -> Integer:
    """row index of lowermost occupied cell"""
    indices = toindices(patch)
    return max((i for i, j in indices), default=0)


def leftmost(patch: Patch) -> Integer:
    """column index of leftmost occupied cell"""
    indices = toindices(patch)
    return min((j for i, j in indices), default=0)


def rightmost(patch: Patch) -> Integer:
    """column index of rightmost occupied cell"""
    indices = toindices(patch)
    return max((j for i, j in indices), default=0)


def ulcorner(patch: Patch) -> IntegerTuple:
    """index of upper left corner"""
    indices = toindices(patch)
    if not indices:
        return (0, 0)
    return (min(i for i, j in indices), min(j for i, j in indices))


def lrcorner(patch: Patch) -> IntegerTuple:
    """index of lower right corner"""
    indices = toindices(patch)
    if not indices:
        return (0, 0)
    return (max(i for i, j in indices), max(j for i, j in indices))


def urcorner(patch: Patch) -> IntegerTuple:
    """index of upper right corner"""
    indices = toindices(patch)
    if not indices:
        return (0, 0)
    return (min(i for i, j in indices), max(j for i, j in indices))


def llcorner(patch: Patch) -> IntegerTuple:
    """index of lower left corner"""
    indices = toindices(patch)
    if not indices:
        return (0, 0)
    return (max(i for i, j in indices), min(j for i, j in indices))


def height(piece: Piece) -> Integer:
    """height of grid or patch"""
    try:
        if isinstance(piece, tuple):
            return len(piece)
        if not piece:
            return 0
        return lowermost(piece) - uppermost(piece) + 1
    except TypeError:
        return 0


def width(piece: Piece) -> Integer:
    """width of grid or patch"""
    try:
        if isinstance(piece, tuple):
            return len(piece[0]) if piece else 0
        if not piece:
            return 0
        return rightmost(piece) - leftmost(piece) + 1
    except (TypeError, IndexError):
        return 0


def mostcolor(element: Element) -> Integer:
    """most common color"""
    if not element:
        return 0
    try:
        values = [v for r in element for v in r] if isinstance(element, tuple) else [v for v, _ in element]
        if not values:
            return 0
        return Counter(values).most_common(1)[0][0]
    except (TypeError, IndexError, ValueError):
        return 0


def shift(patch: Patch, directions: IntegerTuple) -> Patch:
    """shift patch"""
    # Robustness checks
    if not patch:
        return patch
    if not isinstance(directions, tuple) or len(directions) != 2:
        return patch  # Return unmodified patch if directions are invalid

    try:
        di, dj = directions
        # Check if patch is an Object (has colors) or just Indices
        if isinstance(next(iter(patch))[1], tuple):
            return frozenset((value, (i + di, j + dj)) for value, (i, j) in patch)
        return frozenset((i + di, j + dj) for i, j in patch)
    except (TypeError, IndexError, StopIteration, ValueError):
        # Catch other potential errors with malformed patches
        return patch


def dneighbors(loc: IntegerTuple) -> Indices:
    """directly adjacent indices"""
    try:
        return frozenset({(loc[0] - 1, loc[1]), (loc[0] + 1, loc[1]), (loc[0], loc[1] - 1), (loc[0], loc[1] + 1)})
    except (TypeError, IndexError):
        return frozenset()


def ineighbors(loc: IntegerTuple) -> Indices:
    """diagonally adjacent indices"""
    try:
        return frozenset(
            {(loc[0] - 1, loc[1] - 1), (loc[0] - 1, loc[1] + 1), (loc[0] + 1, loc[1] - 1), (loc[0] + 1, loc[1] + 1)}
        )
    except (TypeError, IndexError):
        return frozenset()


def neighbors(loc: IntegerTuple) -> Indices:
    """adjacent indices"""
    return dneighbors(loc) | ineighbors(loc)


def palette(element: Element) -> FrozenSet[Integer]:
    """colors occurring in object or grid"""
    if not element:
        return frozenset()
    try:
        if isinstance(element, tuple):
            return frozenset({v for r in element for v in r})
        return frozenset({v for v, _ in element})
    except (TypeError, ValueError):
        return frozenset()


def sizefilter(container: Container, n: Integer) -> FrozenSet:
    """filter items by size"""
    filtered = set()
    try:
        for item in container:
            if hasattr(item, "__len__") and len(item) == n:
                filtered.add(item)
    except TypeError:
        pass
    return frozenset(filtered)


def asindices(grid: Grid) -> Indices:
    """indices of all grid cells"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return frozenset()
    return frozenset((i, j) for i in range(len(grid)) for j in range(len(grid[0])))


def ofcolor(grid: Grid, value: Integer) -> Indices:
    """indices of all grid cells with value"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return frozenset()
    return frozenset((i, j) for i, r in enumerate(grid) for j, v in enumerate(r) if v == value)


def crop(grid: Grid, start: IntegerTuple, dims: IntegerTuple) -> Grid:
    """subgrid specified by start and dimension"""
    try:
        if not isinstance(start, tuple) or len(start) != 2:
            return tuple()
        if not isinstance(dims, tuple) or len(dims) != 2:
            return tuple()

        si, sj = start
        h, w = dims
        return tuple(r[sj : sj + w] for r in grid[si : si + h])
    except (TypeError, IndexError):
        return tuple()


def recolor(value: Integer, patch: Patch) -> Object:
    """recolor patch"""
    return frozenset((value, index) for index in toindices(patch))


def normalize(patch: Patch) -> Patch:
    """moves upper left corner to origin"""
    if not patch:
        return patch
    return shift(patch, (-uppermost(patch), -leftmost(patch)))


def objects(grid: Grid, univalued: Boolean, diagonal: Boolean, without_bg: Boolean) -> Objects:
    """objects occurring on the grid"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return frozenset()

    bg = mostcolor(grid) if without_bg else None
    objs, occupied = set(), set()
    h, w = len(grid), len(grid[0])
    diagfun = neighbors if diagonal else dneighbors

    for r in range(h):
        for c in range(w):
            loc = (r, c)
            if loc in occupied:
                continue

            val = grid[r][c]
            if val == bg:
                continue

            obj, cands = set(), {loc}
            while cands:
                cand = cands.pop()
                if not (0 <= cand[0] < h and 0 <= cand[1] < w) or cand in occupied:
                    continue

                v = grid[cand[0]][cand[1]]
                if (val == v) if univalued else (v != bg):
                    obj.add((v, cand))
                    occupied.add(cand)
                    cands.update(diagfun(cand))
            if obj:
                objs.add(frozenset(obj))
    return frozenset(objs)


def partition(grid: Grid) -> Objects:
    """each cell with the same value part of the same object"""
    colors = palette(grid)
    return frozenset(ofcolor(grid, c) for c in colors)


def fgpartition(grid: Grid) -> Objects:
    """each cell with the same value part of the same object without background"""
    colors = palette(grid) - {mostcolor(grid)}
    return frozenset(ofcolor(grid, c) for c in colors)


def square(piece: Piece) -> Boolean:
    """whether the piece forms a square"""
    h, w = height(piece), width(piece)
    if h == 0 or w == 0:
        return False

    is_solid = h * w == len(toindices(piece))
    return h == w and is_solid


def vline(patch: Patch) -> Boolean:
    """whether the piece forms a vertical line"""
    return width(patch) == 1 and len(toindices(patch)) > 0


def hline(patch: Patch) -> Boolean:
    """whether the piece forms a horizontal line"""
    return height(patch) == 1 and len(toindices(patch)) > 0


def hmatching(a: Patch, b: Patch) -> Boolean:
    """whether there exists a row for which both patches have cells"""
    try:
        return not set(i for i, j in toindices(a)).isdisjoint(set(i for i, j in toindices(b)))
    except (TypeError, ValueError):
        return False


def vmatching(a: Patch, b: Patch) -> Boolean:
    """whether there exists a column for which both patches have cells"""
    try:
        return not set(j for i, j in toindices(a)).isdisjoint(set(j for i, j in toindices(b)))
    except (TypeError, ValueError):
        return False


def manhattan(a: Patch, b: Patch) -> Integer:
    """closest manhattan distance between two patches"""
    ind_a, ind_b = toindices(a), toindices(b)
    if not ind_a or not ind_b:
        return 0
    return min(abs(ai - bi) + abs(aj - bj) for ai, aj in ind_a for bi, bj in ind_b)


def adjacent(a: Patch, b: Patch) -> Boolean:
    """whether two patches are adjacent"""
    return manhattan(a, b) == 1


def bordering(patch: Patch, grid: Grid) -> Boolean:
    """whether a patch is adjacent to a grid border"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return False
    inds = toindices(patch)
    if not inds:
        return False

    h, w = len(grid), len(grid[0])
    return uppermost(patch) == 0 or leftmost(patch) == 0 or lowermost(patch) == h - 1 or rightmost(patch) == w - 1


def centerofmass(patch: Patch) -> IntegerTuple:
    """center of mass"""
    inds = toindices(patch)
    if not inds:
        return (0, 0)

    row_sum = sum(i for i, j in inds)
    col_sum = sum(j for i, j in inds)
    return (row_sum // len(inds), col_sum // len(inds))


def numcolors(element: Element) -> Integer:
    """number of colors occurring in object or grid"""
    return len(palette(element))


def color(obj: Object) -> Integer:
    """color of object"""
    if not obj:
        return 0
    # Assumes a univalued object
    return next(iter(obj), (0,))[0]


def toobject(patch: Patch, grid: Grid) -> Object:
    """object from patch and grid"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return frozenset()
    h, w = len(grid), len(grid[0])
    return frozenset((grid[i][j], (i, j)) for i, j in toindices(patch) if 0 <= i < h and 0 <= j < w)


def asobject(grid: Grid) -> Object:
    """conversion of grid to object"""
    return toobject(asindices(grid), grid)


def rot90(grid: Grid) -> Grid:
    """quarter clockwise rotation"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    return tuple(zip(*grid[::-1]))


def rot180(grid: Grid) -> Grid:
    """half rotation"""
    return rot90(rot90(grid))


def rot270(grid: Grid) -> Grid:
    """quarter anticlockwise rotation"""
    return rot180(rot90(grid))


def hmirror(piece: Piece) -> Piece:
    """mirroring along horizontal"""
    if isinstance(piece, tuple):
        return tuple(piece[::-1])
    d = uppermost(piece) + lowermost(piece)
    try:
        if isinstance(next(iter(piece), (0, (0, 0)))[1], tuple):
            return frozenset((v, (d - i, j)) for v, (i, j) in piece)
        return frozenset((d - i, j) for i, j in piece)
    except (TypeError, IndexError, StopIteration):
        return piece


def vmirror(piece: Piece) -> Piece:
    """mirroring along vertical"""
    if isinstance(piece, tuple):
        return tuple(row[::-1] for row in piece)
    d = leftmost(piece) + rightmost(piece)
    try:
        if isinstance(next(iter(piece), (0, (0, 0)))[1], tuple):
            return frozenset((v, (i, d - j)) for v, (i, j) in piece)
        return frozenset((i, d - j) for i, j in piece)
    except (TypeError, IndexError, StopIteration):
        return piece


def dmirror(piece: Piece) -> Piece:
    """mirroring along diagonal"""
    if isinstance(piece, tuple):
        return tuple(zip(*piece))
    a, b = ulcorner(piece)
    try:
        if isinstance(next(iter(piece), (0, (0, 0)))[1], tuple):
            return frozenset((v, (j - b + a, i - a + b)) for v, (i, j) in piece)
        return frozenset((j - b + a, i - a + b) for i, j in piece)
    except (TypeError, IndexError, StopIteration):
        return piece


def cmirror(piece: Piece) -> Piece:
    """mirroring along counterdiagonal"""
    if isinstance(piece, tuple):
        return rot270(dmirror(rot90(piece)))
    return vmirror(dmirror(vmirror(piece)))


def fill(grid: Grid, value: Integer, patch: Patch) -> Grid:
    """fill value at indices"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    h, w = len(grid), len(grid[0])
    g = [list(r) for r in grid]
    for i, j in toindices(patch):
        if 0 <= i < h and 0 <= j < w:
            g[i][j] = value
    return tuple(tuple(r) for r in g)


def paint(grid: Grid, obj: Object) -> Grid:
    """paint object to grid"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    h, w = len(grid), len(grid[0])
    g = [list(r) for r in grid]
    try:
        for value, (i, j) in obj:
            if 0 <= i < h and 0 <= j < w:
                g[i][j] = value
    except (TypeError, ValueError):
        pass
    return tuple(tuple(r) for r in g)


def underfill(grid: Grid, value: Integer, patch: Patch) -> Grid:
    """fill value at indices that are background"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    bg = mostcolor(grid)
    return fill(grid, value, toindices(patch) & ofcolor(grid, bg))


def underpaint(grid: Grid, obj: Object) -> Grid:
    """paint object to grid where there is background"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    bg = mostcolor(grid)
    h, w = len(grid), len(grid[0])
    g = [list(r) for r in grid]
    try:
        for value, (i, j) in obj:
            if 0 <= i < h and 0 <= j < w:
                if g[i][j] == bg:
                    g[i][j] = value
    except (TypeError, ValueError):
        pass  # Ignore malformed objects
    return tuple(tuple(r) for r in g)


def hupscale(grid: Grid, factor: Integer) -> Grid:
    """upscale grid horizontally"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    safe_factor = max(1, min(factor, 20))
    return tuple(tuple(v for v in r for _ in range(safe_factor)) for r in grid)


def vupscale(grid: Grid, factor: Integer) -> Grid:
    """upscale grid vertically"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    safe_factor = max(1, min(factor, 20))
    g = tuple()
    for row in grid:
        g += (row,) * safe_factor
    return g


def upscale(element: Element, factor: Integer) -> Element:
    """upscale object or grid"""
    safe_factor = max(1, min(factor, 20))
    if isinstance(element, tuple):
        return vupscale(hupscale(element, safe_factor), safe_factor)

    if not element:
        return frozenset()

    try:
        normed_obj = normalize(element)
        o = set()
        for value, (i, j) in normed_obj:
            for io in range(safe_factor):
                for jo in range(safe_factor):
                    o.add((value, (i * safe_factor + io, j * safe_factor + jo)))
        return shift(frozenset(o), ulcorner(element))
    except (TypeError, ValueError, IndexError):
        return element


def downscale(grid: Grid, factor: Integer) -> Grid:
    """downscale grid"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    safe_factor = max(1, factor)
    return tuple(tuple(r[::safe_factor]) for r in grid[::safe_factor])


def hconcat(a: Grid, b: Grid) -> Grid:
    """concatenate two grids horizontally"""
    is_a_grid = isinstance(a, tuple) and (not a or isinstance(a[0], tuple))
    is_b_grid = isinstance(b, tuple) and (not b or isinstance(b[0], tuple))
    if not is_a_grid:
        return b if is_b_grid else tuple()
    if not is_b_grid:
        return a

    if not a:
        return b
    if not b:
        return a

    if len(a) != len(b):
        return a  # Incompatible height

    return tuple(tuple(row_a) + tuple(row_b) for row_a, row_b in zip(a, b))


def vconcat(a: Grid, b: Grid) -> Grid:
    """concatenate two grids vertically"""
    is_a_grid = isinstance(a, tuple) and (not a or isinstance(a[0], tuple))
    is_b_grid = isinstance(b, tuple) and (not b or isinstance(b[0], tuple))
    if not is_a_grid:
        return b if is_b_grid else tuple()
    if not is_b_grid:
        return a

    if not a:
        return b
    if not b:
        return a

    if len(a[0]) != len(b[0]):
        return a  # Incompatible width

    return tuple(a) + tuple(b)


def subgrid(patch: Patch, grid: Grid) -> Grid:
    """smallest subgrid containing object"""
    return crop(grid, ulcorner(patch), shape(patch))


def hsplit(grid: Grid, n: Integer) -> Tuple:
    """split grid horizontally"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    n = max(1, n)
    h, w = len(grid), len(grid[0]) // n
    return tuple(crop(grid, (0, w * i), (h, w)) for i in range(n)) if w > 0 else (grid,)


def vsplit(grid: Grid, n: Integer) -> Tuple:
    """split grid vertically"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    n = max(1, n)
    h, w = len(grid) // n, len(grid[0])
    return tuple(crop(grid, (h * i, 0), (h, w)) for i in range(n)) if h > 0 else (grid,)


def cellwise(a: Grid, b: Grid, fallback: Integer) -> Grid:
    """cellwise match of two grids"""
    if shape(a) != shape(b):
        return a
    h, w = shape(a)
    g = []
    for i in range(h):
        row = []
        for j in range(w):
            row.append(a[i][j] if a[i][j] == b[i][j] else fallback)
        g.append(tuple(row))
    return tuple(g)


def replace(grid: Grid, replacee: Integer, replacer: Integer) -> Grid:
    """color substitution"""
    if not isinstance(grid, tuple):
        return tuple()
    return tuple(tuple(replacer if v == replacee else v for v in r) for r in grid)


def switch(grid: Grid, a: Integer, b: Integer) -> Grid:
    """color switching"""
    if not isinstance(grid, tuple):
        return tuple()
    return tuple(tuple(v if (v != a and v != b) else (b if v == a else a) for v in r) for r in grid)


def center(patch: Patch) -> IntegerTuple:
    """center of the patch"""
    return (uppermost(patch) + height(patch) // 2, leftmost(patch) + width(patch) // 2)


def position(a: Patch, b: Patch) -> IntegerTuple:
    """relative position between two patches"""
    ia, ja = center(a)
    ib, jb = center(b)
    di, dj = ib - ia, jb - ja
    return (0 if di == 0 else di // abs(di), 0 if dj == 0 else dj // abs(dj))


def index(grid: Grid, loc: IntegerTuple) -> Integer:
    """Gets the color at a specific location in a grid."""
    if not isinstance(loc, tuple) or len(loc) != 2:
        return -1  # Return -1 for invalid location format
    try:
        i, j = loc
        h, w = shape(grid)
        return grid[i][j] if 0 <= i < h and 0 <= j < w else -1
    except (TypeError, IndexError):
        return -1


def canvas(value: Integer, dimensions: IntegerTuple) -> Grid:
    """grid construction"""
    try:
        h, w = dimensions
        safe_h = max(0, min(h, 50))
        safe_w = max(0, min(w, 50))
        return tuple(tuple(value for _ in range(safe_w)) for _ in range(safe_h))
    except (TypeError, ValueError):
        return tuple()


def corners(patch: Patch) -> Indices:
    """indices of corners"""
    if not toindices(patch):
        return frozenset()
    return frozenset({ulcorner(patch), urcorner(patch), llcorner(patch), lrcorner(patch)})


def connect(a: IntegerTuple, b: IntegerTuple) -> Indices:
    """line between two points"""
    if not isinstance(a, tuple) or len(a) != 2 or not isinstance(b, tuple) or len(b) != 2:
        return frozenset()
    try:
        ai, aj = a
        bi, bj = b
        si, ei = sorted((ai, bi))
        sj, ej = sorted((aj, bj))
        if ai == bi:
            return frozenset((ai, j) for j in range(sj, ej + 1))
        if aj == bj:
            return frozenset((i, aj) for i in range(si, ei + 1))
        if (bi - ai) == (bj - aj):
            return frozenset(
                zip(
                    range(ai, bi + (1 if bi > ai else -1), 1 if bi > ai else -1),
                    range(aj, bj + (1 if bj > aj else -1), 1 if bj > aj else -1),
                )
            )
        if (bi - ai) == -(bj - aj):
            return frozenset(
                zip(
                    range(ai, bi + (-1 if bi < ai else 1), -1 if bi < ai else 1),
                    range(aj, bj + (-1 if bj < aj else 1), -1 if bj < aj else 1),
                )
            )
        return frozenset()
    except (TypeError, IndexError):
        return frozenset()


def cover(grid: Grid, patch: Patch) -> Grid:
    """remove object from grid"""
    if not isinstance(grid, tuple) or not grid:
        return tuple()
    return fill(grid, mostcolor(grid), toindices(patch))


def trim(grid: Grid) -> Grid:
    """trim border of grid"""
    if height(grid) < 3 or width(grid) < 3:
        return grid
    return tuple(r[1:-1] for r in grid[1:-1])


def move(grid: Grid, obj: Object, offset: IntegerTuple) -> Grid:
    """move object on grid"""
    if not isinstance(grid, tuple) or not grid:
        return tuple()
    return paint(cover(grid, obj), shift(obj, offset))


def tophalf(grid: Grid) -> Grid:
    """upper half of grid"""
    if not isinstance(grid, tuple) or not grid:
        return tuple()
    return grid[: len(grid) // 2]


def bottomhalf(grid: Grid) -> Grid:
    """lower half of grid"""
    if not isinstance(grid, tuple) or not grid:
        return tuple()
    return grid[len(grid) // 2 + len(grid) % 2 :]


def lefthalf(grid: Grid) -> Grid:
    """left half of grid"""
    if not isinstance(grid, tuple) or not grid:
        return tuple()
    return rot270(tophalf(rot90(grid)))


def righthalf(grid: Grid) -> Grid:
    """right half of grid"""
    if not isinstance(grid, tuple) or not grid:
        return tuple()
    return rot270(bottomhalf(rot90(grid)))


def vfrontier(location: IntegerTuple) -> Indices:
    """vertical frontier"""
    try:
        return frozenset((i, location[1]) for i in range(-50, 51))
    except (TypeError, IndexError):
        return frozenset()


def hfrontier(location: IntegerTuple) -> Indices:
    """horizontal frontier"""
    try:
        return frozenset((location[0], j) for j in range(-50, 51))
    except (TypeError, IndexError):
        return frozenset()


def backdrop(patch: Patch) -> Indices:
    """indices in bounding box of patch"""
    if not patch:
        return frozenset()
    si, sj = ulcorner(patch)
    ei, ej = lrcorner(patch)
    return frozenset((i, j) for i in range(si, ei + 1) for j in range(sj, ej + 1))


def delta(patch: Patch) -> Indices:
    """indices in bounding box but not part of patch"""
    if not patch:
        return frozenset()
    return backdrop(patch) - toindices(patch)


def gravitate(source: Patch, destination: Patch) -> IntegerTuple:
    """direction to move source until adjacent to destination"""
    try:
        s_inds, d_inds = toindices(source), toindices(destination)
        if not s_inds or not d_inds:
            return (0, 0)

        si, sj = center(s_inds)
        di, dj = center(d_inds)
        i, j = (0, 0)

        if not vmatching(s_inds, d_inds):
            i = 1 if si < di else -1
        if not hmatching(s_inds, d_inds):
            j = 1 if sj < dj else -1
        if i == 0 and j == 0:
            i = 1 if si < di else -1  # Default move if perfectly aligned

        gi, gj = 0, 0
        c = 0
        temp_source = s_inds
        while not adjacent(temp_source, d_inds) and c < 42:
            c += 1
            gi += i
            gj += j
            temp_source = shift(temp_source, (i, j))
        return (gi, gj)
    except (TypeError, ValueError, IndexError):
        return (0, 0)


def inbox(patch: Patch) -> Indices:
    """inbox for patch"""
    if not patch:
        return frozenset()
    u, l = ulcorner(patch)
    o, r = lrcorner(patch)
    return frozenset((i, j) for i in range(u + 1, o) for j in range(l + 1, r))


def outbox(patch: Patch) -> Indices:
    """outbox for patch"""
    if not patch:
        return frozenset()
    ai, aj = uppermost(patch) - 1, leftmost(patch) - 1
    bi, bj = lowermost(patch) + 1, rightmost(patch) + 1
    vlines = {(i, aj) for i in range(ai, bi + 1)} | {(i, bj) for i in range(ai, bi + 1)}
    hlines = {(ai, j) for j in range(aj, bj + 1)} | {(bi, j) for j in range(aj, bj + 1)}
    return frozenset(vlines | hlines)


def box(patch: Patch) -> Indices:
    """outline of patch"""
    if not patch:
        return frozenset()
    ai, aj = ulcorner(patch)
    bi, bj = lrcorner(patch)
    vlines = {(i, aj) for i in range(ai, bi + 1)} | {(i, bj) for i in range(ai, bi + 1)}
    hlines = {(ai, j) for j in range(aj, bj + 1)} | {(bi, j) for j in range(aj, bj + 1)}
    return frozenset(vlines | hlines)


def shoot(start: IntegerTuple, direction: IntegerTuple) -> Indices:
    """line from starting point and direction"""
    try:
        return connect(start, (start[0] + 42 * direction[0], start[1] + 42 * direction[1]))
    except (TypeError, IndexError):
        return frozenset()


def occurrences(grid: Grid, obj: Object) -> Indices:
    """locations of occurrences of object in grid"""
    if not obj or not isinstance(grid, tuple) or not grid:
        return frozenset()
    occs = set()
    try:
        normed = normalize(obj)
        h, w = len(grid), len(grid[0])
        oh, ow = shape(normed)
        if oh == 0 or ow == 0:
            return frozenset()

        h2, w2 = h - oh + 1, w - ow + 1
        for i in range(h2):
            for j in range(w2):
                sub_grid_obj = toobject(shift(backdrop(normed), (i, j)), grid)
                if sub_grid_obj == shift(normed, (i, j)):
                    occs.add((i, j))
    except (TypeError, IndexError, ValueError):
        pass
    return frozenset(occs)


def frontiers(grid: Grid) -> Objects:
    """set of frontiers"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return frozenset()
    h, w = len(grid), len(grid[0])
    hfrontiers = frozenset(
        frozenset((grid[i][j], (i, j)) for j in range(w)) for i in range(h) if len(set(grid[i])) == 1
    )
    vfrontiers = frozenset(
        frozenset((grid[i][j], (i, j)) for i in range(h))
        for j in range(w)
        if len(set(grid[i][j] for i in range(h))) == 1
    )
    return hfrontiers | vfrontiers


def compress(grid: Grid) -> Grid:
    """removes frontiers from grid"""
    if not isinstance(grid, tuple) or not grid or not isinstance(grid[0], tuple):
        return tuple()
    ri = [i for i, r in enumerate(grid) if len(set(r)) == 1]
    ci = [j for j, c in enumerate(zip(*grid)) if len(set(c)) == 1]
    return tuple(tuple(v for j, v in enumerate(r) if j not in ci) for i, r in enumerate(grid) if i not in ri)


def hperiod(obj: Object) -> Integer:
    """horizontal periodicity"""
    if not obj:
        return 0
    w = width(obj)
    try:
        normalized = normalize(obj)
        for p in range(1, w + 1):
            offsetted = shift(normalized, (0, -p))
            pruned = frozenset({cell for cell in offsetted if cell[1][1] >= 0})
            if pruned.issubset(normalized):
                return p
    except (TypeError, IndexError, ValueError):
        pass
    return w


def vperiod(obj: Object) -> Integer:
    """vertical periodicity"""
    if not obj:
        return 0
    h = height(obj)
    try:
        normalized = normalize(obj)
        for p in range(1, h + 1):
            offsetted = shift(normalized, (-p, 0))
            pruned = frozenset({cell for cell in offsetted if cell[1][0] >= 0})
            if pruned.issubset(normalized):
                return p
    except (TypeError, IndexError, ValueError):
        pass
    return h
