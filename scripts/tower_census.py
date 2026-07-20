#!/usr/bin/env python3
"""tower_census.py -- exact census of the Salem tower.

For a monic reciprocal integer polynomial P (coefficients high -> low), compute
the tower L_k = |Res(P, x^(2^k)+1)| exactly (integer companion-matrix repeated
squaring + Bareiss determinant), verify the perfect-square law, factor sqrt(L_k),
and classify every prime factor by its rung mechanism:

  * split (r = 1):      a root of order 2^(k+1) in F_q itself  =>  q = 1 mod 2^(k+1)
  * extension (r > 1):  the root lives in F_{q^m}; ord_{2^(k+1)}(q) divides m
  * squared prime:      either horizontal (several root pairs at one rung) or
                        vertical (order fails to lift from q to q^2 -- the
                        rung-local Wieferich phenomenon)

Usage:
  python3 tower_census.py                     # Lehmer's polynomial, rungs 1..9
  python3 tower_census.py 1,1,0,-1,-1,-1,-1,-1,0,1,1 8
"""
import math
import sys

try:
    from sympy import factorint
except ImportError:
    sys.exit("needs sympy: pip install sympy")

LEHMER = [1, 1, 0, -1, -1, -1, -1, -1, 0, 1, 1]


def tower_values(cf_high_to_low, K):
    """L_k = |det(M^(2^k) + I)| for the companion matrix M of P, k = 1..K."""
    low = cf_high_to_low[::-1]
    d = len(low) - 1
    M = [[0] * d for _ in range(d)]
    for i in range(1, d):
        M[i][i - 1] = 1
    for i in range(d):
        M[i][d - 1] = -low[i]

    def matmul(A, B):
        return [[sum(A[i][k] * B[k][j] for k in range(d)) for j in range(d)]
                for i in range(d)]

    def det_bareiss(Ain):
        A = [r[:] for r in Ain]
        sign, prev = 1, 1
        for k in range(d - 1):
            if A[k][k] == 0:
                for r in range(k + 1, d):
                    if A[r][k]:
                        A[k], A[r] = A[r], A[k]
                        sign = -sign
                        break
                else:
                    return 0
            for i in range(k + 1, d):
                for j in range(k + 1, d):
                    A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
            prev = A[k][k]
        return sign * A[d - 1][d - 1]

    I = [[int(i == j) for j in range(d)] for i in range(d)]
    cur = [r[:] for r in M]
    out = []
    for _ in range(K):
        cur = matmul(cur, cur)
        out.append(abs(det_bareiss([[cur[i][j] + I[i][j] for j in range(d)]
                                    for i in range(d)])))
    return out


def rung_of(cf_high_to_low, q, kmax=64):
    """Rungs k where P has a root of exact order 2^(k+1) in F_qbar:
    deg gcd(P, x^(2^k)+1) mod q per k."""
    low = [c % q for c in cf_high_to_low[::-1]]
    d = len(low) - 1

    def pmul(A, B):
        C = [0] * (len(A) + len(B) - 1)
        for i, a in enumerate(A):
            if a:
                for j, b in enumerate(B):
                    C[i + j] = (C[i + j] + a * b) % q
        for i in range(len(C) - 1, d - 1, -1):
            c = C[i]
            if c:
                C[i] = 0
                for j in range(d + 1):
                    C[i - d + j] = (C[i - d + j] - c * low[j]) % q
        return [c % q for c in C[:d]]

    def gcd_deg(A):
        def norm(v):
            v = [c % q for c in v]
            while v and v[-1] == 0:
                v.pop()
            return v
        a, b = norm(low[:]), norm(A)
        while b:
            inv = pow(b[-1], q - 2, q)
            while len(a) >= len(b):
                c = (a[-1] * inv) % q
                sh = len(a) - len(b)
                for j in range(len(b)):
                    a[sh + j] = (a[sh + j] - c * b[j]) % q
                a = norm(a)
                if not a:
                    break
            a, b = b, a
        return len(a) - 1 if a else -1

    cur = [0, 1] + [0] * (d - 2)
    hits = []
    for k in range(kmax):
        t = cur[:]
        t[0] = (t[0] + 1) % q
        g = gcd_deg(t)
        if g > 0:
            hits.append((k, g))
        cur = pmul(cur, cur)
    return hits


def main():
    cf = LEHMER if len(sys.argv) < 2 else [int(c) for c in sys.argv[1].split(",")]
    K = 9 if len(sys.argv) < 3 else int(sys.argv[2])
    print(f"P (high->low) = {cf},  rungs 1..{K}")
    for k, L in enumerate(tower_values(cf, K), start=1):
        s = math.isqrt(L)
        if s * s != L:
            print(f"  k={k}: L_k NOT a perfect square (P not reciprocal?)")
            continue
        if s == 1:
            print(f"  k={k}: sqrt(L_k) = 1  (defect rung)")
            continue
        f = factorint(s)
        parts = []
        for q, e in sorted(f.items()):
            m = 2 ** (k + 1)
            grade = "split" if q % m == 1 else f"r={_ord(q, m)}"
            sq = f" SQUARED^{e}" if e >= 2 else ""
            parts.append(f"{q} ({grade}{sq})")
        print(f"  k={k}: sqrt(L_k) = {s} = " + " * ".join(parts))


def _ord(q, m):
    o, v = 1, q % m
    while v != 1:
        v = (v * q) % m
        o += 1
        if o > m:
            return "?"
    return o


if __name__ == "__main__":
    main()
