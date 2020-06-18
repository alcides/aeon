import z3
import pandas as pd

from .z3_evaluator import Z3Evaluator


def get_values(n, random_qflra=False, condition=None, history=False):
    l = list()
    lista_not = list()
    for i in range(n):
        z3.set_option("smt.random_seed", i)
        z3.set_option("smt.arith.random_initial_value", True)

        if random_qflra:
            s = z3.With('qflra', random_seed=i).solver()
        else:
            s = z3.Solver()

        x = z3.Int("x")
        if history:
            for not_stmt in lista_not:
                s.add(not_stmt)
        s.add(condition(x))
        r = s.check()
        if r == z3.sat:
            v = int(str(s.model()[x]))
            # TODO: real parser, like https://stackoverflow.com/questions/12598408/z3-python-getting-python-values-from-model
            l.append(v)
            if history:
                lista_not.append(x != v)
        else:
            break
    return l


def get_aeon_values(n, condition=None):
    import random
    l = []
    s = z3.Solver()
    x = z3.Int("x")
    s.add(condition(x))
    for i in range(n):
        for i in range(1000):
            v = round(random.gauss(0, 0.05) * 7500)
            s.push()
            s.add(x == v)
            r = s.check()
            s.pop()
            if r == z3.sat:
                l.append(v)
                break
    return l


def semantic_pairwise_distance_sum(xs):
    result = []
    i = 0
    for x in xs:
        result.append(0)
        for y in xs:
            result[i] += abs(x - y)
        i += 1
    return result


def pairwise_distance_sum(xs):
    result = []
    i = 0
    for x in xs:
        result.append(0)
        for y in xs:
            result[i] += (1 - pow(0.99, abs(x - y)))
        i += 1
    return result


def write_to_file(file_name, cond, values, distances, semantics, model=None):

    file_name = file_name + '_' + cond + '.csv'

    with open(file_name, 'w') as writer:
        if model:
            writer.write("Version,")
        writer.write('Typee,Individual,Diversity,Semantic Diversity\r\n')

        for value, distance, semantic in zip(values, distances, semantics):
            writer.write(model + ",")
            line = '{},{},{},{}\r\n'.format(cond, value, distance, semantic)
            writer.write(line)


def run_z3():

    # The same types we want to generate
    integer = ('Integer', lambda x: x != z3.Int("y"))
    natural = ('Natural', lambda x: x > 0)
    mod_four = ('M4', lambda x: x % 4 == 0)
    gt0_lt10 = ('LT10', lambda x: z3.And(x > 0, x < 10))

    conditions = [integer, natural, mod_four, gt0_lt10]

    for pretty_cond, cond in conditions:

        default_values = get_values(100, condition=cond)
        default_distance = pairwise_distance_sum(default_values)
        default_semantic = semantic_pairwise_distance_sum(default_values)

        qflra_values = get_values(100, random_qflra=True, condition=cond)
        qflra_distance = pairwise_distance_sum(qflra_values)
        qflra_semantic = semantic_pairwise_distance_sum(qflra_values)

        history_qflra_values = get_values(100,
                                          random_qflra=True,
                                          condition=cond,
                                          history=True)
        history_qflra_distance = pairwise_distance_sum(history_qflra_values)
        history_qflra_semantic = semantic_pairwise_distance_sum(
            history_qflra_values)

        history_aeon_values = get_aeon_values(100, cond)
        history_aeon_distance = pairwise_distance_sum(history_aeon_values)
        history_aeon_semantic = semantic_pairwise_distance_sum(
            history_aeon_values)

        write_to_file('aeon/evaluation/z3/default', pretty_cond,
                      default_values, default_distance, default_semantic,
                      'default')
        write_to_file('aeon/evaluation/z3/qflra', pretty_cond, qflra_values,
                      qflra_distance, qflra_semantic, 'qflra')
        write_to_file('aeon/evaluation/z3/qflra-history', pretty_cond,
                      history_qflra_values, history_qflra_distance,
                      history_qflra_semantic, 'qflra-history')
        write_to_file('aeon/evaluation/z3/aeon', pretty_cond,
                      history_aeon_values, history_aeon_distance,
                      history_aeon_semantic, 'aeon')

    Z3Evaluator().process()
