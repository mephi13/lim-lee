from dataclasses import dataclass, field
from typing import List, Optional
from random import randrange
from blessed import Terminal
from sympy import randprime, isprime, nextprime
from Crypto.PublicKey import ECC
import math
import functools
import operator


@dataclass
class CombFastExponentiation:
    a: int
    """Length of a single block"""
    b: int
    """Length of a single subblock"""
    l: int
    """Length of the exponent e"""
    S: int
    """Maximium number of precomputed group elements"""
    h: int = field(init=False)
    """Number of blocks l/a"""
    v: int = field(init=False)
    """Number of subblocks a/b"""

    a_last: int = field(init=False)
    """Number of bits in the last block"""
    v_last: int = field(init=False)
    """Number of subblocks of the last block"""
    b_last: int = field(init=False)
    """Number of bits in the leading subblock of the last block"""
    b_leading: int = field(init=False)
    """Number of bits in the leading subblock"""


    def __post_init__(self):
        self.h = math.ceil(self.l/self.a)
        self.v = math.ceil(self.a/self.b)
        self.a_last = self.l - self.a * (self.h - 1)
        self.v_last = math.ceil(self.a_last/self.b)
        self.b_last = self.a_last - self.b * (self.v_last - 1)
        self.b_leading = self.a - self.b * (self.v - 1)
        assert self._debinarize(self._binarize(4321, 32)) == 4321

    def precompute(self, g, p=None):
        # 0 <= j <= v
        # 1 <= u <= 2^h
        # G[j][u] = (G[j-1][u])^(2^b) = (G[0][u])^(2^(jb))
        # I_j,k = sum_i=0^h-1 (e_i,j,k)*2^i

        r = []
        # generate empty array G
        G = [[1 for y in range(0, 2 ** self.h)] for x in range(0, self.v + 1)]

        # precalculate 2^a
        two_to_a = pow(2, (self.a), p) if p else pow(2, (self.a))

        # Calculate r values
        for i in range(self.h):
            if isinstance(g, int):
                r.append(pow(g, pow(two_to_a, i, p), p))
            elif isinstance(g, ECC.EccPoint):
                r.append( g * pow(two_to_a, i) )

        # Populate array G
        for u in range(1, 2 ** self.h):

            # handle base case G[0][u]
            u_binary = self._binarize(u, self.h)

            if isinstance(g, int):
                G[0][u] = functools.reduce(operator.mul, map(lambda x,y: x ** y, r, u_binary)) % p
            elif isinstance(g, ECC.EccPoint):
                G[0][u] = functools.reduce(operator.add, map(lambda x,y: x * y, r, u_binary))

            for j in range(1, self.v):
                if isinstance(g, int):
                    G[j][u] = pow((G[j-1][u]), 2 ** b, p) 
                elif isinstance(g, ECC.EccPoint):
                    G[j][u] = (G[j-1][u]) * (2 ** b) 

        self.G = G
        self.g = g
        self.p = p

    def _binarize(self, u, length):
            u_bin_str = format((u), 'b')
            list = [int(x) for x in u_bin_str]
            list.reverse()
            u_binary = list + [0 for x in range(length - len(u_bin_str))]
            return u_binary

    def _debinarize(self, bin):
        out = 0
        for i in range(len(bin)):
            out += bin[i] * 2 ** i
        return out

    def print_G(self, p=1):
        p = self.p if self.p else p
        out: list = ["G:"]
        term = Terminal()
        max_size = math.ceil(math.log10(p))
        out.append("")
        if self.G:
            for row in self.G:
                new_out = "| "
                for column in row:
                    new_out += format((column), f"{max_size}") + ", "
                out.append(new_out + "|")
        last_line = "-" * len(out[2])
        out[1] = last_line
        out.append(last_line)
        print("\n".join(out))

    def fast_exponentiation(self, e):
        # set R = 1
        e_blocked = self.divide_exponent_into_block(e)

        if isinstance(self.g, int):
            R = 1
            p = self.p
            e = e % p
            for k in range(self.b - 1, 0 - 1, -1):
                R = pow(R, 2, p)
                for j in range(self.v - 1, 0 - 1, -1):
                    I_jk = (self.get_index(e_blocked, j, k))
                    if I_jk > 0:
                        R = (R * self.G[j][I_jk]) % p

        elif isinstance(self.g, ECC.EccPoint):
            R = ECC.EccPoint(0, 0, curve="NIST P-521") # neutral element of addition 
            for k in range(self.b - 1, 0 - 1, -1):
                R = R.double()
                for j in range(self.v - 1, 0 - 1, -1):
                    I_jk = (self.get_index(e_blocked, j, k))

                    if I_jk > 0:
                        R = (R + self.G[j][I_jk]) 
        return R

    def get_index(self, e_blocked, j, k):
        out = []
        for i in range(0, self.h):
            if i == self.h-1 and j == self.v_last - 1:
                width = self.b_last
            if j == self.v - 1:
                width = self.b_leading
            else:
                width = self.b
            if i == self.h -1 and j+1 > self.v_last:
                break 
            if k < width:
                out.append(e_blocked[i][j][k])
            else:
                out.append(0)

        return self._debinarize(out)

    def divide_exponent_into_block(self, e):
        e_bin = self._binarize(e, self.l)
        e_blocked = []
        for i in range(0, self.h):
            row = (i * self.a)
            e_blocked.append([])
            for j in range(0, self.v if i != self.h - 1 else self.v_last):
                column = max(j, 0) * self.b
                if i == self.h-1 and j == self.v_last - 1:
                    width = self.b_last
                if j == self.v - 1:
                    width = self.b_leading
                else:
                    width = self.b
                e_blocked[i].append((e_bin[(row + column) : ((row + column + width)) ]))
        
        return e_blocked

def calculate_optimal_parameters(S, l):
    """Bruteforce for finding optimal a and b parameters"""
    opt_a = 0
    opt_b = 0
    opt_cost = None
    opt_scost = None
    for a in range(1, l+1):
        for b in range(1, a+1):
            h = math.ceil(l/a)
            v = math.ceil(a/b)
            a_last = l - a * (h - 1)
            v_last = math.ceil(a_last/b)
            b_last = a_last - b * (v_last - 1)

            # we assume that cost for squating and multiplication is the same
            squaring_cost = b - 1
            multiplication_cost = ((2 ** (h - 1)) - 1) / (2 ** (h - 1)) * (a - a_last) + ((2 ** (h)) - 1) / (2 ** (h)) * a_last - 1

            cost = squaring_cost + multiplication_cost

            storage_cost = ((2 ** h) - 1) * v_last + ((2 ** (h - 1)) - 1) * (v - v_last)

            if storage_cost > S:
                continue
            if not opt_cost or opt_cost > cost:
                opt_cost = cost
                opt_scost = storage_cost
                opt_a = a
                opt_b = b

    return opt_a, opt_b, opt_cost, opt_scost

def gen_strong_prime(min, max, randomize_bin_len = False, p =None, p_t = None):
    if p:
        p_t = (p - 1) // 2
    elif p_t:
        p =  2*p_t + 1
    else:
        p = 0
        min_v = min - 2
        max_v = max - 2
        while not isprime(p):
            if randomize_bin_len:
                min_v = randrange(min - 2,max - 2)
                max_v = min_v + 1
            p_t = randprime(2 ** min_v, 2 ** max_v)
            p = 2*p_t + 1

    return (p, p_t)

l = 64
p, _ = gen_strong_prime(0, l)
g = 3
e = randrange(0, 2 ** l) 
S = 100

a, b, cost, scost = calculate_optimal_parameters(S, l)
print(a, b, cost, scost)
instance= CombFastExponentiation(a, b, l, S)

print(g, p)
instance.precompute(g, p)
print(instance)
print(len(instance.G) * (len(instance.G[0]) - 1)) 
e_blocked = instance.divide_exponent_into_block(e)

for i in e_blocked:
    i.reverse()
    print(i)

print(g, e, instance.fast_exponentiation(e))
print(pow(g, e, p))

curve = ECC.generate(curve="NIST P-521")
basepoint = curve.pointQ

instance.precompute(basepoint)
result = instance.fast_exponentiation(e)

print(result.xy)

print((basepoint * e) == result)