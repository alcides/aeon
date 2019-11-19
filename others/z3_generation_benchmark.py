import z3


def get(i, random_qflra=False, is_real=False):
    z3.set_option("smt.random_seed", i)
    z3.set_option("smt.arith.random_initial_value", True)
    if random_qflra:
        s = z3.With('qflra', random_seed=i).solver()
    else:
        s = z3.Solver()
    if is_real:
        x = z3.Real("x")
    else:
        x = z3.Int("x")
    s.add(x > 0)
    s.check()
    return float(
        str(s.model()[x])
    )  # TODO: real parser, like https://stackoverflow.com/questions/12598408/z3-python-getting-python-values-from-model


def get_values(n, **kwargs):
    return [get(i, **kwargs) for i in range(n)]


def parwise_distance_sum(xs):
    s = 0
    for x in xs:
        for y in xs:
            s += abs(x - y)
    return s / 2


print("z3 int default:", parwise_distance_sum(get_values(100)))
print("z3 int qflra:", parwise_distance_sum(get_values(100,
                                                       random_qflra=True)))
print("z3 real default:", parwise_distance_sum(get_values(100, is_real=True)))
print("z3 real qflra:",
      parwise_distance_sum(get_values(100, random_qflra=True, is_real=True)))
