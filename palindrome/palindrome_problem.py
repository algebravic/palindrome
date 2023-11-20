"""
Solve the palindrome problem.
"""
from typing import List, Tuple, Iterable, Dict
from .numbers import SAT, Digit, Number, all_solutions, make_number, get_number

def get_answer(base: int, real_vars: List[Tuple[str, int, int]]) -> str:
    """
    Generate a printable answer to the problem.
    """

    reps = {_: get_number(_, base, real_vars) for _ in ['a', 'b', 'c']}

    values = [int(reps[_], base) for _ in ['a', 'b', 'c']]

    if values[0] + values[1] != values[2]:
        print("Solution fails")

    return reps['a'] + ' + ' + reps['b'] + ' = ' + reps['c']

def digit_problem(mval: int, nval: int, rval: int, base: int, use_all: bool = False):
    """
    Use SAT to solve the palindrome problem.

    A + B = C

    where A, B and C are number in base b, with no leading 0's,
    the string of digits ABC is a palindrome,
    and all b values of the the digits actually appear.
    """

    if not (all((isinstance(_, int) for _ in [mval, nval, rval]))
                and mval > 0 and nval > 0 and rval > 0):
        raise ValueError("Bad digit lengths")

    outlen = max(mval, nval)

    if rval < outlen or rval > outlen + 1:
        raise ValueError("Impossible lengths")

    sat = SAT()

    anum = make_number('a', sat, mval, base)
    bnum = make_number('b', sat, nval, base)
    cnum = make_number('c', sat, rval, base)

    # Top digit != 0

    for elt in [anum, bnum, cnum]:
        elt._value[-1].forbid(0)
    
    # palindrome

    alldigs = (list(reversed(anum._value)) + 
                   list(reversed(bnum._value)) + 
                   list(reversed(cnum._value)))
        
    split = len(alldigs) // 2

    top = list(reversed(alldigs[-split:]))

    for left, right in zip(top, alldigs[: split]):
        left.equal(right)
    
    if use_all:
        sat.extend([[elt._digits[ind] for elt in alldigs] for ind in range(base)])

    # Do the addition
                    
    result, carry = anum.add(bnum)

    if rval == outlen:

        # carry = 0

        sat.append([-carry])

    elif rval == outlen + 1:

        # carry = top digit = 1

        sat.extend([[carry], [cnum._value[-1]._digits[1]]])

    for left, right in zip(result._value, cnum._value):
        left.equal(right)

    return sat, anum, bnum, cnum


def solve_palindrome(mval: int, nval: int, rval: int, base: int = 10,
                     use_all: bool = True,
                     all_models: bool = True,
                     trace: int = 0,
                     solver = 'cadical') -> List[str]:
    """
    Use a SAT solver to solve the palindrome problem.
    """

    sat, _, _, _ = digit_problem(mval, nval, rval, base, use_all = use_all)

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

        answers.append(get_answer(base, real_vars))

    return answers

def decomposition(num: int, base: int = 10) -> Iterable[Tuple[int, int, int]]:
    if num < 2 * base - 1:
        raise ValueError(f"{num} < {2 * base - 1}")

    # B = C or C-1, A + B + C = num

    # if B = C, then A = num - 2 * C
    # So 2 * C <= num - 1, and A <= C
    # So 2 * C >= num - C, or C >= ceil(num / 3)

    for cnum in range((num + 2) // 3, (num + 1)// 2):
        anum = num - 2 * cnum
        bnum = cnum
        yield (anum, bnum, cnum)
        if anum != bnum:
            yield(bnum, anum, cnum)

    for cnum in range(1 + num // 3, 1 + num // 2):
        anum = num - 2 * cnum + 1
        bnum = cnum - 1
        yield anum, bnum, cnum
        if anum != bnum:
            yield bnum, anum, cnum

def try_palindrome(num: int, base: int = 10) -> Dict[Tuple[int, int, int], List[str]]:

    return {_: solve_palindrome(*_) for _ in decomposition(num, base)}
    
    
