#!/usr/bin/env python
from dataclasses import dataclass, field
from typing import List, Optional
from random import randrange
from blessed import Terminal
from sympy import randprime, isprime, nextprime
from Crypto.PublicKey import ECC
import math
import argparse
import time
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
        G = [[0 for y in range(0, 2 ** self.h)] for x in range(0, self.v)]

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
        squarings = 0
        multiplications = 0

        if isinstance(self.g, int):
            R = 1
            p = self.p
            e = e % p
            for k in range(self.b - 1, 0 - 1, -1):
                R = pow(R, 2, p)
                squarings += 1
                for j in range(self.v - 1, 0 - 1, -1):
                    I_jk = (self.get_index(e_blocked, j, k))
                    if I_jk > 0:
                        R = (R * self.G[j][I_jk]) % p
                        multiplications += 1

        elif isinstance(self.g, ECC.EccPoint):
            R = ECC.EccPoint(0, 0, curve="NIST P-521") # neutral element of addition 
            for k in range(self.b - 1, 0 - 1, -1):
                R = R.double()
                squarings += 1
                for j in range(self.v - 1, 0 - 1, -1):
                    I_jk = (self.get_index(e_blocked, j, k))

                    if I_jk > 0:
                        R = (R + self.G[j][I_jk]) 
                        multiplications += 1
        return R, squarings, multiplications

    def get_index(self, e_blocked, j, k):
        out = []
        for i in range(0, self.h):
            if i == self.h-1 and j == self.v_last - 1:
                width = self.b_last
            elif j == self.v - 1:
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
            b_leading = a - b * (v - 1)

            # we assume that cost for squaring and multiplication is the same
            squaring_cost = b - 1
            multiplication_cost = (((2 ** (h - 1)) - 1) / (2 ** (h - 1))) * (a - a_last) + (((2 ** (h)) - 1) / (2 ** (h))) * (a_last - 1)

            cost = squaring_cost + multiplication_cost

            storage_cost = ((2 ** h) - 1) * v + ((2 ** (h - 1)) - 1) * (v - v_last)

            if storage_cost > S:
                continue
            if not opt_cost or opt_cost > cost:
                opt_cost = cost
                opt_scost = storage_cost
                opt_a = a
                opt_b = b

    return opt_a, opt_b, opt_cost, opt_scost

def gen_prime(min, max):
    p = 0
    min_v = min 
    max_v = max 
    while not isprime(p):
        p = randprime(2 ** min_v, 2 ** max_v)
    return p

def print_blocks(blocks):
    t = Terminal()
    l = len(str(blocks[0]))
    l2 = len(str(blocks[0][-1]))
    l3 = len(str(blocks[0][0]))
    l4 = len(str(blocks[-1][-1]))
    block_a ="\n<" + "-" * ((l-3)//2) + t.red("a") + "-" * ((l-2)//2) +">\n"
    block_b_le ="<" + "-" * ((l2-5)//2) + t.green("b_le") + "-" * ((l2-4)//2) +">"
    block_b = (l - t.length(block_b_le) - l3 - 1) * " " + "<" + "-" * ((l3-1)//2) + t.green("b") + "-" * ((l3-2)//2) +">\n"

    blocks_str = block_a + block_b_le + block_b
    for i, row in enumerate(blocks):
        row.reverse()
        if len(str(row)) == len(str(blocks[0])) and i != len(blocks) - 1:
            blocks_str += str(row)
            if i == 0:
                blocks_str += "↑" + "\n"
            elif i == len(blocks) //2 :
                blocks_str += term.blue("h") + "\n"
            else:
                blocks_str += "|" + "\n"
        else:
            empty = (len(str(blocks[0])) - len(str(row))) 
            blocks_str += " " * empty + str(row)
            blocks_str += "↓" + "\n"
            blocks_str += empty * " " + "<" + "-" * ((l4-5)//2) + t.green("b_la") + "-" * ((l4-4)//2) +">\n"
            blocks_str += empty * " " + "<" + "-" * ((l-8 - empty)//2) + t.red("a_last") + "-" * ((l-7 - empty)//2) +">\n"
    return blocks_str

if __name__== "__main__":
    parser = argparse.ArgumentParser(description='Lim/Lee comb exponentiation algorhitm for EC and integers.')
    parser.add_argument("--length", "-l", type=int, help="Bit length of exponent", default=128)
    parser.add_argument("--integer", "-i", action="count", help="Calculate exponentiation on integers (EC is default)", default=0)
    parser.add_argument("--storage","-S", type=int, help="Maximum stored elements", default=100)
    parser.add_argument("--generator", "-g", type=int,help="Generator for integer calculations", default=None)
    parser.add_argument("--exponent", "-e", type=int,help="Exponent", default=None)
    parser.add_argument("--plength", "-p", type=int,help="Bit length of prime defining Zp for integer calculations", default=128)

    args = parser.parse_args()

    calc_ec = not args.integer
    if calc_ec:
        curve = ECC.generate(curve="NIST P-521")
        G = curve.pointQ
 
    e = args.exponent if args.exponent else randrange(1, 2 ** args.length) 
    l = e.bit_length()
    p = gen_prime(0, args.plength)
    g = args.generator if args.generator else randrange(0, 2 ** randrange(1, l)) 
   
    S = args.storage

    term = Terminal()

    print("-" * term.width)
    print(f"{term.bold_underline('Stage 1')}")
    print(f"Calculating optimal a, b parameters for given S={term.brown(str(S))} and l={term.blue(str(l))}")
    a, b, cost, scost = calculate_optimal_parameters(S, l)
    print("." * term.width)
    print(f"a={term.red(str(a))}")
    print(f"b={term.green(str(b))}")
    print(f"operation cost={term.yellow(str(cost))}")
    print(f"storage cost={term.brown(str(scost))}")

    print("-" * term.width)
    print(f"{term.bold_underline('Stage 2')}")

    if not calc_ec:
        print(f"Precomputing multiples of generator g={term.orange(str(g))} with field size p={term.purple(str(p))}")  
    else:
        print(f"Precomputing multiples of basepoing G={term.orange(str(G.xy))} of curve {curve.curve}")  


    comb= CombFastExponentiation(a, b, l, S)
    print("." * term.width)

    start = time.time()
    if not calc_ec:
        comb.precompute(g, p)
    else:
        comb.precompute(G)
    stop = time.time() - start

    print(f"Calculated parameters for precomputing: {term.bold_red(str(comb))}")
    
    storage = functools.reduce(lambda x,y: x + len(y), comb.G, 0) 
    print(f"Calculated number of stored elements: {term.brown_bold(str(storage))}")
    print(f"Precomputing time: {term.yellow(str(round(stop, 5)))}")

    print("-" * term.width)
    print(f"{term.bold_underline('Stage 3')}")
    if not calc_ec:
        print(f"Finding the value g^e for g={term.orange(str(g))} and e={term.pink(str(e))}")  
    else:
        print(f"Finding the value G*e for G={term.orange(str(G.xy))} and e={term.pink(str(e))}")  
    print("." * term.width)

    e_blocks = comb.divide_exponent_into_block(e)
    print(f"Representation of the exponent in blocks: ")
    print(term.bold(print_blocks(e_blocks)))

    start = time.time()
    result, s, m = comb.fast_exponentiation(e)
    stop = time.time() - start

    print(f"Online Calculations time: {term.yellow(str(round(stop, 10)))}")
    print(f"Squarings: {term.yellow(str(s))}")
    print(f"Multiplications: {term.yellow(str(m))}")

    if not calc_ec:
        print(f"Result: {term.underline_bold_green(str(result))}") if pow(g, e, p) == result else print(f"Wrong result: {term.underline_bold_red(str(result))}") 
        print(f"{result} == {pow(g, e, p)}? " + str(pow(g, e, p) == result))
    else:
        print(f"Result: {term.underline_bold_green(str(result.xy))}") if G * e == result else print(f"Wrong result: {term.underline_bold_red(str(result.xy))}") 
        print(f"{result.xy} == {(G * e).xy}? " + str((G * e) == result))
