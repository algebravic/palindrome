from pysat.formula import CNF, IDPool
from pysat.solvers import Solver
from pysat.card import EncType, CardEnc
from itertools import product
from string import digits, ascii_uppercase
from typing import List, Tuple, Union, Dict, Generator, Iterable, Callable
import math

class SAT:
    """
    A Sat formula class.
    """

    def __init__(self, cardtype: str = 'seqcounter'):

        self._cnf = CNF()
        self._pool = IDPool()
        self._cardinality = getattr(EncType, cardtype)
        self._zero = self._pool._next()
        self.append([- self._zero])

    def append(self, lst):
        'The append operator'
        self._cnf.append(lst)

    def extend(self, lst):
        'The extend operator for the sat pool'
        self._cnf.extend(lst)

    @property
    def zero(self):
        'A zero value of a bit'
        return self._zero

    @property
    def cardinality(self):
        'The cardinality argument'
        return self._cardinality

    @property
    def pool(self):
        'The variable pool'
        return self._pool

def equivalent(lit1: int, lit2: int, sat: SAT):
    'SAT for equivalence of two sequences'

    sat.extend([[-lit1, lit2], [-lit2, lit1]])

class Digit:
    pass

class Digit:

    def _make_separate(self):

        self._parent.extend(CardEnc.equals(
            lits=self._digits,
            encoding = self._parent.cardinality,
            vpool = self._parent.pool,
            bound=1))

    def __init__(self, digits: List[int], parent: SAT, enforce = True):

        if not (isinstance(digits, List)
                    and all((isinstance(_, int) and _ >= 1 for _ in digits))
                    and len(set(digits)) == len(digits) # distinct
                    and len(digits) >= 2):
            raise ValueError("Base must be an int >= 2")

        if not isinstance(parent, SAT):
            raise ValueError("Parent must be a SAT instance")

        self._base = len(digits)
        self._digits = digits.copy()
        self._parent = parent

        if enforce:
            self._make_separate()

    @property
    def parent(self):
        """
        The SAT parent of this class
        """
        return self._parent

    @property
    def base(self):
        """
        The number base.
        """
        return self._base

    def _compatible(self, other: Digit):
        """
        Check if the argument is compatible with self.
        """
        return(isinstance(other, Digit)
               and other.parent == self.parent
               and other.base == self._base)

    def add_with_carry(self, other: Digit, carry: int):
        """
        Add two digits with a starting carry
        """

        if not(isinstance(carry, int) and carry >= 1):
            raise ValueError('Carry must be a SAT variable')

        if not self._compatible(other):
            raise ValueError('Incompatible digits')

        out = [self._parent.pool._next() for _ in range(self._base)]

        out_carry = self._parent.pool._next()

        for left, right, extra in product(range(self._base),
                                              range(self._base),
                                              range(2)):
            result = left + right + extra

            outdig = result % self._base
            outcar = result // self._base

            cardig = out_carry if outcar else - out_carry
            incarry = carry if extra else - carry

            self._parent.append([- incarry, - self._digits[left],
                                          - other._digits[right], out[outdig]])

            self._parent.append([- incarry, - self._digits[left],
                                          - other._digits[right], cardig])

        return Digit(out, self._parent), out_carry

    def add(self, other:Digit):
        'Add two digits'

        return self.add_with_carry(other, self._parent.zero)

    def add_carry(self, carry: int):
        'Add a carry bit'

        if not(isinstance(carry, int) and carry >= 1):
            raise ValueError('Carry must be a SAT variable')

        out = [self._parent.pool._next() for _ in range(self._base)]

        out_carry = self._parent.pool._next()

        for left, extra in product(range(self._base),
                                       range(2)):
            result = left + extra

            outdig = result % self._base
            outcar = result // self._base

            cardig = out_carry if outcar else - out_carry
            incarry = carry if extra else - carry

            self._parent.append([-incarry, -self._digits[left],
                                          out[outdig]])

            self._parent.append([-incarry, -self._digits[left],
                                          cardig])

        return Digit(out, self._parent), out_carry

    def max(self, other: Digit):
        """
        Calculate the max of two digits.
        """
        if not self._compatible(other):
            raise ValueError('Incompatible argument')
        out = [self._parent.pool._next() for _ in range(self._base)]

        for left, right in product(range(self._base), range(self._base)):
            result = max(left, right)
            self._parent.append([- self._digits[left], - other._digits[right],
                                      out[result]])

        return Digit(out, self._parent)

    def min(self, other: Digit):
        """
        Calculate the min of two digits.
        """
        if not self._compatible(other):
            raise ValueError('Incompatible argument')
        out = [self._parent.pool._next() for _ in range(self._base)]

        for left, right in product(range(self._base), range(self._base)):
            result = min(left, right)

            self._parent.append([- self._digits[left], - other._digits[right],
                                      out[result]])

        return Digit(out, self._parent)
    
    def double(self):
        """
        Double a digit
        """
        return self.add_with_carry(self, 0)

    def equal(self, other: Digit):
        'Generate SAT for equality'

        if not self._compatible(other):
            raise ValueError('Incompatible argument')

        for lit1, lit2 in zip(self._digits, other._digits):
            equivalent(lit1, lit2, self._parent)

    def forbid(self, value: int):
        'Forbid a value for this digit'
        if not (value >= 0 and value < self.base):
            raise ValueError("Improper forbidden value")

        self._parent.append([- self._digits[value]])
                                 
    def require(self, value: int):
        'Forbid a value for this digit'
        if not (value >= 0 and value < self.base):
            raise ValueError("Improper required value")

        self._parent.append([self._digits[value]])

    @property
    def zero(self):
        return self._parent._zero
                                 
class Number:
    pass

class Number:

    def __init__(self, digits: List[Digit]):

        """A base b number"""

        if not (isinstance(digits, list)
                    and all((isinstance(_, Digit) for _ in digits))
                    and len(digits) > 0
                    and all((digits[0]._compatible(_) for _ in digits[1:]))):
            raise ValueError("Input must be a non empty list of compatible digits")

        self._value = digits
        self._len = len(digits)
        self._base = digits[0]._base
        self._zero = digits[0].zero

    def __len__(self):

        return self._len

    def _compatible(self, other: Number):

        return isinstance(other, Number) and self._base == other._base

    def add_with_carry(self, other: Number, carry: int):

        if not self._compatible(other):
            raise ValueError("Incomparable addends")

        left, right = self._value, other._value
        if len(left) > len(right):
            left, right = right, left

        incarry = carry

        outdigs = []

        for ldig, rdig in zip(left, right):

            nxtdig, incarry = ldig.add_with_carry(rdig, incarry)
            outdigs.append(nxtdig)

        for dig in right[len(left): ]:

            nxtdig, incarry = dig.add_carry(incarry)
            outdigs.append(nxtdig)

        return Number(outdigs), incarry

    def add(self, other: Number):
        'add two numbers'

        return self.add_with_carry(other, self._zero)
    
def make_number(name: str, sat: SAT, lval: int, base: int):

    if not (isinstance(lval, int)
                and lval > 0
                and isinstance(name, str)
                and isinstance(base, int)
                and base >= 2
                and isinstance(sat, SAT)):
        raise ValueError("Illegal arguments")

    return Number ([Digit([sat.pool.id((name, ind, _)) for _ in range(base)], sat)
                        for ind in range(lval)])

def all_solutions(name: str,
                  cnf: CNF,
                  use_timer: bool = True,
                  trace: int = 0) -> Generator[Tuple[List[int], Dict[str, Union[int, float]]],
                                                       None, None]:
    """
    Generate all solutions to a particular version of the problem, by using incremental SAT solving.
    """

    solve = Solver(name = name,
                   bootstrap_with = cnf,
                   use_timer = use_timer)

    accum_time = 0.0

    while True:

        this_status = solve.solve()
        this_stats = solve.accum_stats()
        accum_time += solve.time()
        this_stats.update({'time': accum_time})
        model = solve.get_model()

        if trace > 1:
            print("Solution stats = {}".format(this_stats))
        
        yield model, this_stats

        if model is not None:
            solve.add_clause([- _ for _ in model]) # block this solution

        else:
            return

def get_number(name: str, base: int, real_vars: List[Tuple[str, int, int]]) -> str:

    pairs = [(ind, val) for stem, ind, val in real_vars if stem == name]

    inds, digs = zip(*sorted(pairs, key = lambda _: _[0], reverse=True))

    linds = len(inds)

    if inds != tuple(range(linds - 1, -1, -1)):
        print(f"Gaps: {name}, {inds}")

    trans = digits + ascii_uppercase
    return ''.join((trans[_] for _ in digs))

def bitonic(num: int) -> Iterable[Tuple[int, int]]:
    """
    Bitonic network, per Wikipedia
    """
    kind = 2
    while kind <= num:
        jind = kind // 2
        while jind > 0:
            for ind in range(num):
                lval = ind ^ jind
                if lval > ind:
                    if (ind & kind) == 0:
                        yield ind, lval
                    else:
                        yield lval, ind
            jind //= 2
        kind *= 2

def oddeven_merge_step(length):
    t = math.ceil(math.log2(length))
    q = 2 ** (t - 1)
    r = 0
    d = 1

    while d > 0:
        for i in range(length - d):
            if i & 1 == r:
                yield (i, i + d)

        d = q - 1
        q //= 2
        r = 1

def batcher(n: int) -> Iterable[Tuple[int, int]]:
    """
    Batcher sort
    """
    pnt = 1
    while pnt < n:
        k = pnt
        while k >= 1:
            for j in range(k % pnt, n - k, 2 * k):
                for i in range(k):
                    if (i+j) // (2 * pnt) == (i + j + k) // (2 * pnt):
                        yield i + j, i + j + k
            k = k // 2
        pnt *= 2

def oddeven_merge_sort(length):
    t = math.ceil(math.log2(length))

    p = 2 ** (t - 1)

    while p > 0:
        q = 2 ** (t - 1)
        r = 0
        d = p

        while d > 0:
            for i in range(length - d):
                if i & p == r:
                    yield (i, i + d)

            d = q - p
            q //= 2
            r = p
        p //= 2
        
def sort_digits(digits: List[Digit],
                network: Callable[[int], Iterable[Tuple[int, int]]] = oddeven_merge_sort) -> List[Digit]:
    """
    Use a sorting network to sort the digits
    """

    new_digits = digits.copy()

    for left, right in network(len(digits)):

        new_digits[left], new_digits[right] = new_digits[left].min(new_digits[right]), new_digits[left].max(new_digits[right])

    return new_digits

                
