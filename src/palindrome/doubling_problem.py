"""
Solve the problem of doubling a number rearranges the bag of digits.
"""
from typing import List, Tuple
from .numbers import SAT, Digit, Number, all_solutions, make_number, get_number, sort_digits
from numpy import base_repr

def solve_doubling(size: int, base: int = 10, try_carry: bool = False,
                   solver: str = 'cadical',
                   all_models: bool = True,
                   trace: int = 0):
    """
    Solve the doubling problem.

    First make a number of the right size.
    Remember to forbid the top digit to be 0.
    Either forbid the top digit to be >= half the base,
    or forbid the carry from doubling to be 1.
    Then sort it, to get a normal form
    Then produce the doubled number.
    Then sort that.
    Then require equality of each digit
    """
    sat = SAT()

    num = make_number('a', sat, size, base)

    num._value[-1].forbid(0)

    if not try_carry:
        for ind in range((base + 1) // 2, base):
            num._value[-1].forbid(ind)

    sort_num = sort_digits(num._value)

    new_num, carry = num.add(num) # double it

    sat.append([-carry])

    sort_new_num = sort_digits(new_num._value)

    for left, right in zip(sort_num, sort_new_num):
        left.equal(right)

    solutions = all_solutions(solver, sat._cnf, trace = trace)

    if all_models:

        allmodels, stats = zip(*solutions)
        final_stat = stats[-1]
        models = allmodels[: -1]
    else:
        model, final_stat = next(solutions)
        models = [model] if model is not None else []

    if trace > 0:
        print(f"status = {len(models) > 0}, stats = {final_stat}")

    answers = []
    for model in models:

        true_vars = [sat.pool.obj(_) for _ in model if _ > 0]
        real_vars = [_ for _ in true_vars if _ is not None]

        value = get_number('a', base, real_vars)

        sort_value = sorted(value)

        doubled = sorted(base_repr(int(value, base) * 2, base=base))

        if sort_value != doubled:
            print(f"Solution {value} fails: {doubled}!")

        answers.append(value)

    return answers
