#!/usr/bin/env python3
"""Expected values of the worked instances of NLAlib/Ops/Examples/WorkedInstances/.

Each function computes, with exact rational arithmetic and from the textbook formula of the
operation (not from the tree of the routine), the output and the number of arithmetic
operations that the corresponding Lean theorem states. The Lean theorems derive the same
literals under the execution rules of the library; `scripts/test_worked_instances.py` checks
that the literals printed here occur in the Lean sources.

The number of structural instructions (index arithmetic, operand resolution, loop rounds,
frames, allocations) has no source outside the library. The totals stated in Lean are
regression values and are not computed here.

Usage: python3 scripts/worked_instances.py
"""
from fractions import Fraction as F


def lean_list(values):
    """A list of rationals as a Lean list literal."""
    def one(v):
        v = F(v)
        return str(v.numerator) if v.denominator == 1 else f"{v.numerator} / {v.denominator}"
    return "[" + ", ".join(one(v) for v in values) + "]"


def vector_sum():
    """Entrywise sum of two vectors of length 3: one addition per entry."""
    x, y = [F(1), F(2), F(3)], [F(10), F(20), F(30)]
    out = [a + b for a, b in zip(x, y)]
    return {"output": lean_list(out), "add": len(x)}


def strided_scaling():
    """x[::2] *= 5 on a buffer of five cells: one multiplication per selected cell; the
    other cells are untouched."""
    buf, a, n, inc = [F(1), F(100), F(2), F(200), F(3)], F(5), 3, 2
    out = list(buf)
    for k in range(n):
        out[inc * k] = out[inc * k] * a
    return {"buffer": lean_list(out), "mul": n}


def dense_matvec():
    """y = A x for a 2 x 3 matrix stored column by column (Fortran order): for each of the
    m rows, a sum of n products accumulated from a literal zero."""
    A = [[F(1), F(2), F(3)], [F(4), F(5), F(6)]]
    x = [F(1), F(1), F(2)]
    m, n = len(A), len(x)
    column_major = [A[i][j] for j in range(n) for i in range(m)]
    y = [sum(A[i][j] * x[j] for j in range(n)) for i in range(m)]
    return {"storage": lean_list(column_major), "output": lean_list(y),
            "lit": m, "mul": m * n, "add": m * n, "scratch_cells": 1}


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def integrator():
    """x_N = (I + h A)^N x_0 with A = [[0, 1], [-1, 0]], h = 1/2, N = 2: one product with A
    and one update per step, and one scratch vector of length n."""
    A = [[F(0), F(1)], [F(-1), F(0)]]
    h, N, x0 = F(1, 2), 2, [F(4), F(8)]
    n = len(x0)
    G = [[(1 if i == j else 0) + h * A[i][j] for j in range(n)] for i in range(n)]
    x = list(x0)
    for _ in range(N):
        x = [sum(G[i][j] * x[j] for j in range(n)) for i in range(n)]
    return {"output": lean_list(x), "matvec": N, "axpy": N, "scratch_cells": n}


def countdown(start, cap=5):
    """Move a counter to a second cell one unit at a time, for at most `cap` rounds, testing
    before each round. Returns the final cells and the tests, decrements and increments made.

    `operand` is the library's convention for operand resolutions: one per test made, four per
    round (two operations with one input and one output each), and one more when the loop ends
    at its cap, where the exit is charged the address of the test although no test is made."""
    x, y, tests, rounds = start, 0, 0, 0
    stopped_by_test = False
    while rounds < cap:
        tests += 1
        if x == 0:
            stopped_by_test = True
            break
        x, y, rounds = x - 1, y + 1, rounds + 1
    operand = tests + 4 * rounds + (0 if stopped_by_test else 1)
    return {"cells": f"twoCells {x} {y}", "dec": rounds, "inc": rounds, "tests": tests,
            "operand": operand}


INSTANCES = {
    "VectorSum": vector_sum(),
    "Strided": strided_scaling(),
    "Matvec": dense_matvec(),
    "Integrator": integrator(),
    "EarlyExit (stop at a false test)": countdown(2),
    "EarlyExit (stop at the cap)": countdown(7),
}


def main():
    for name, values in INSTANCES.items():
        print(name)
        for key, value in values.items():
            print(f"  {key}: {value}")


if __name__ == "__main__":
    main()
