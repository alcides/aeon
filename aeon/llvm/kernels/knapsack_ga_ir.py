"""Build LLVM IR for a 0-1 knapsack genetic algorithm (single function + kernel).

All generations run inside one kernel body so a CUDA launch does not bounce
back to the host between generations — only the final scalar result is copied.
"""

from __future__ import annotations

import llvmlite.binding as llvm
import llvmlite.ir as ir


def _rand(builder: ir.IRBuilder, rng_ptr: ir.Value) -> ir.Value:
    x = builder.load(rng_ptr)
    t1 = builder.mul(x, ir.Constant(ir.IntType(32), 1664525))
    t2 = builder.add(t1, ir.Constant(ir.IntType(32), 1013904223))
    builder.store(t2, rng_ptr)
    return builder.and_(t2, ir.Constant(ir.IntType(32), 0x7FFFFFFF))


def _mod_nonneg(builder: ir.IRBuilder, value: ir.Value, modulus: ir.Value) -> ir.Value:
    rem = builder.srem(value, modulus)
    neg = builder.icmp_signed("<", rem, ir.Constant(ir.IntType(32), 0))
    fixed = builder.add(rem, modulus)
    return builder.select(neg, fixed, rem)


def build_knapsack_ga_module(*, nvptx: bool = False) -> ir.Module:
    module = ir.Module(name="knapsack_ga")
    if nvptx:
        module.triple = "nvptx64-nvidia-cuda"
        module.data_layout = (
            "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-"
            "f32:32:32-f64:64:64-v16:16:16-v32:32:32-v64:64:64-v128:128:128-n32:64"
        )
    else:
        llvm.initialize_native_target()
        module.triple = llvm.get_process_triple()

    i32 = ir.IntType(32)
    i32p = ir.PointerType(i32)
    void = ir.VoidType()

    eval_ty = ir.FunctionType(i32, [i32p, i32p, i32p, i32, i32, i32])
    eval_fn = ir.Function(module, eval_ty, name="eval_one")
    _build_eval_one(eval_fn)

    rnd_ty = ir.FunctionType(i32, [i32p])
    rnd_fn = ir.Function(module, rnd_ty, name="rnd")
    _build_rnd(rnd_fn)

    tour_ty = ir.FunctionType(i32, [i32p, i32, i32p])
    tour_fn = ir.Function(module, tour_ty, name="tournament")
    _build_tournament(tour_fn, rnd_fn)

    xover_ty = ir.FunctionType(void, [i32p, i32p, i32, i32, i32, i32, i32p])
    xover_fn = ir.Function(module, xover_ty, name="crossover_mutate")
    _build_crossover_mutate(xover_fn, rnd_fn)

    ga_ty = ir.FunctionType(i32, [i32p, i32p, i32p, i32p, i32p, i32, i32, i32, i32, i32])
    ga_fn = ir.Function(module, ga_ty, name="knapsack_ga")
    _build_knapsack_ga(ga_fn, eval_fn, tour_fn, xover_fn)

    kernel_ty = ir.FunctionType(void, [i32p, i32p, i32p, i32p, i32p, i32, i32, i32, i32, i32, i32p])
    kernel_fn = ir.Function(module, kernel_ty, name="knapsack_ga__kernel")
    block = kernel_fn.append_basic_block("entry")
    builder = ir.IRBuilder(block)
    args = list(kernel_fn.args)
    result = builder.call(ga_fn, args[:-1])
    builder.store(result, args[-1])
    builder.ret_void()

    if nvptx:
        nvvm = module.add_named_metadata("nvvm.annotations")
        nvvm.add(module.add_metadata([kernel_fn, "kernel", ir.Constant(i32, 1)]))

    return module


def knapsack_ga_ir(*, nvptx: bool = False) -> str:
    return str(build_knapsack_ga_module(nvptx=nvptx))


def _build_rnd(fn: ir.Function) -> None:
    builder = ir.IRBuilder(fn.append_basic_block("entry"))
    builder.ret(_rand(builder, fn.args[0]))


def _build_eval_one(fn: ir.Function) -> None:
    weights, values, pop, indiv, n_items, capacity = fn.args
    i32 = ir.IntType(32)
    entry = fn.append_basic_block("entry")
    cond = fn.append_basic_block("cond")
    body = fn.append_basic_block("body")
    add = fn.append_basic_block("add")
    nxt = fn.append_basic_block("next")
    end = fn.append_basic_block("end")
    builder = ir.IRBuilder(entry)
    base = builder.mul(indiv, n_items)
    j = builder.alloca(i32)
    wsum = builder.alloca(i32)
    vsum = builder.alloca(i32)
    builder.store(ir.Constant(i32, 0), j)
    builder.store(ir.Constant(i32, 0), wsum)
    builder.store(ir.Constant(i32, 0), vsum)
    builder.branch(cond)

    builder.position_at_end(cond)
    jv = builder.load(j)
    builder.cbranch(builder.icmp_signed("<", jv, n_items), body, end)

    builder.position_at_end(body)
    idx = builder.add(base, jv)
    bit = builder.load(builder.gep(pop, [idx]))
    builder.cbranch(builder.icmp_signed("!=", bit, ir.Constant(i32, 0)), add, nxt)

    builder.position_at_end(add)
    w = builder.load(builder.gep(weights, [jv]))
    v = builder.load(builder.gep(values, [jv]))
    builder.store(builder.add(builder.load(wsum), w), wsum)
    builder.store(builder.add(builder.load(vsum), v), vsum)
    builder.branch(nxt)

    builder.position_at_end(nxt)
    builder.store(builder.add(jv, ir.Constant(i32, 1)), j)
    builder.branch(cond)

    builder.position_at_end(end)
    feasible = builder.icmp_signed("<=", builder.load(wsum), capacity)
    builder.ret(builder.select(feasible, builder.load(vsum), ir.Constant(i32, 0)))


def _build_tournament(fn: ir.Function, rnd_fn: ir.Function) -> None:
    fitness, pop_size, rng = fn.args
    builder = ir.IRBuilder(fn.append_basic_block("entry"))
    a = _mod_nonneg(builder, builder.call(rnd_fn, [rng]), pop_size)
    b = _mod_nonneg(builder, builder.call(rnd_fn, [rng]), pop_size)
    fa = builder.load(builder.gep(fitness, [a]))
    fb = builder.load(builder.gep(fitness, [b]))
    builder.ret(builder.select(builder.icmp_signed(">=", fa, fb), a, b))


def _build_crossover_mutate(fn: ir.Function, rnd_fn: ir.Function) -> None:
    pop, next_pop, p1, p2, child, n_items, rng = fn.args
    i32 = ir.IntType(32)
    entry = fn.append_basic_block("entry")
    cond = fn.append_basic_block("cond")
    body = fn.append_basic_block("body")
    end = fn.append_basic_block("end")
    builder = ir.IRBuilder(entry)
    cut = _mod_nonneg(builder, builder.call(rnd_fn, [rng]), n_items)
    base_c = builder.mul(child, n_items)
    base_1 = builder.mul(p1, n_items)
    base_2 = builder.mul(p2, n_items)
    j = builder.alloca(i32)
    builder.store(ir.Constant(i32, 0), j)
    builder.branch(cond)

    builder.position_at_end(cond)
    jv = builder.load(j)
    builder.cbranch(builder.icmp_signed("<", jv, n_items), body, end)

    builder.position_at_end(body)
    from_p1 = builder.icmp_signed("<", jv, cut)
    src_base = builder.select(from_p1, base_1, base_2)
    bit = builder.load(builder.gep(pop, [builder.add(src_base, jv)]))
    mod = _mod_nonneg(builder, builder.call(rnd_fn, [rng]), ir.Constant(i32, 100))
    do_mut = builder.icmp_signed("==", mod, ir.Constant(i32, 0))
    flipped = builder.sub(ir.Constant(i32, 1), bit)
    out = builder.select(do_mut, flipped, bit)
    builder.store(out, builder.gep(next_pop, [builder.add(base_c, jv)]))
    builder.store(builder.add(jv, ir.Constant(i32, 1)), j)
    builder.branch(cond)

    builder.position_at_end(end)
    builder.ret_void()


def _build_knapsack_ga(
    fn: ir.Function,
    eval_fn: ir.Function,
    tour_fn: ir.Function,
    xover_fn: ir.Function,
) -> None:
    weights, values, pop, next_pop, fitness, n_items, capacity, pop_size, generations, seed = fn.args
    i32 = ir.IntType(32)
    entry = fn.append_basic_block("entry")
    gen_cond = fn.append_basic_block("gen.cond")
    gen_body = fn.append_basic_block("gen.body")
    gen_end = fn.append_basic_block("gen.end")
    eval_cond = fn.append_basic_block("eval.cond")
    eval_body = fn.append_basic_block("eval.body")
    eval_end = fn.append_basic_block("eval.end")
    breed_cond = fn.append_basic_block("breed.cond")
    breed_body = fn.append_basic_block("breed.body")
    breed_end = fn.append_basic_block("breed.end")
    copy_cond = fn.append_basic_block("copy.cond")
    copy_body = fn.append_basic_block("copy.body")
    copy_end = fn.append_basic_block("copy.end")

    builder = ir.IRBuilder(entry)
    rng = builder.alloca(i32)
    best = builder.alloca(i32)
    g = builder.alloca(i32)
    i = builder.alloca(i32)
    builder.store(seed, rng)
    builder.store(ir.Constant(i32, 0), best)
    builder.store(ir.Constant(i32, 0), g)
    builder.branch(gen_cond)

    builder.position_at_end(gen_cond)
    gv = builder.load(g)
    builder.cbranch(builder.icmp_signed("<", gv, generations), gen_body, gen_end)

    builder.position_at_end(gen_body)
    builder.store(ir.Constant(i32, 0), i)
    builder.branch(eval_cond)

    builder.position_at_end(eval_cond)
    iv = builder.load(i)
    builder.cbranch(builder.icmp_signed("<", iv, pop_size), eval_body, eval_end)

    builder.position_at_end(eval_body)
    fit = builder.call(eval_fn, [weights, values, pop, iv, n_items, capacity])
    builder.store(fit, builder.gep(fitness, [iv]))
    better = builder.icmp_signed(">", fit, builder.load(best))
    with builder.if_then(better):
        builder.store(fit, best)
    builder.store(builder.add(iv, ir.Constant(i32, 1)), i)
    builder.branch(eval_cond)

    builder.position_at_end(eval_end)
    builder.store(ir.Constant(i32, 0), i)
    builder.branch(breed_cond)

    builder.position_at_end(breed_cond)
    bi = builder.load(i)
    builder.cbranch(builder.icmp_signed("<", bi, pop_size), breed_body, breed_end)

    builder.position_at_end(breed_body)
    p1 = builder.call(tour_fn, [fitness, pop_size, rng])
    p2 = builder.call(tour_fn, [fitness, pop_size, rng])
    builder.call(xover_fn, [pop, next_pop, p1, p2, bi, n_items, rng])
    builder.store(builder.add(bi, ir.Constant(i32, 1)), i)
    builder.branch(breed_cond)

    builder.position_at_end(breed_end)
    n_bits = builder.mul(pop_size, n_items)
    builder.store(ir.Constant(i32, 0), i)
    builder.branch(copy_cond)

    builder.position_at_end(copy_cond)
    ci = builder.load(i)
    builder.cbranch(builder.icmp_signed("<", ci, n_bits), copy_body, copy_end)

    builder.position_at_end(copy_body)
    builder.store(builder.load(builder.gep(next_pop, [ci])), builder.gep(pop, [ci]))
    builder.store(builder.add(ci, ir.Constant(i32, 1)), i)
    builder.branch(copy_cond)

    builder.position_at_end(copy_end)
    builder.store(builder.add(gv, ir.Constant(i32, 1)), g)
    builder.branch(gen_cond)

    builder.position_at_end(gen_end)
    builder.ret(builder.load(best))
