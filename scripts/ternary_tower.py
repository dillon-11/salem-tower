#!/usr/bin/env python3
"""ternary_tower.py -- the 3-power tower of a monic reciprocal polynomial.

N_k = |Res(P, Phi_{3^(k+1)})| = |det(C^(2*3^k) + C^(3^k) + I)|, C the
companion matrix of P. Every N_k is a perfect square (the rung square law
(v^2+v+1)(v^-2+v^-1+1) = (D_s(y)+1)^2; module `TernaryTower` in the Lean
library); ascent is the tripling map D_3(t) = t^3 - 3t.

Usage: python3 ternary_tower.py [kmax]   (Lehmer's polynomial, default kmax=4)
"""
import math
import sys

LEHMER = [1, 1, 0, -1, -1, -1, -1, -1, 0, 1, 1]


def companion(cf):
    d = len(cf) - 1
    M = [[0] * d for _ in range(d)]
    for i in range(1, d):
        M[i][i - 1] = 1
    for i in range(d):
        M[i][d - 1] = -cf[d - i]
    return M


def matmul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def matpow(A, e):
    n = len(A)
    R = [[int(i == j) for j in range(n)] for i in range(n)]
    while e:
        if e & 1:
            R = matmul(R, A)
        A = matmul(A, A)
        e >>= 1
    return R


def det_bareiss(A):
    A = [row[:] for row in A]
    n = len(A)
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for r in range(k + 1, n):
                if A[r][k]:
                    A[k], A[r] = A[r], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    C = companion(LEHMER)
    d = len(C)
    for k in range(1, kmax + 1):
        t = 3 ** k
        Ct, C2t = matpow(C, t), matpow(C, 2 * t)
        S = [[C2t[i][j] + Ct[i][j] + int(i == j) for j in range(d)]
             for i in range(d)]
        N = abs(det_bareiss(S))
        s = math.isqrt(N)
        assert s * s == N, f"rung {k}: not a perfect square"
        print(k, s)


if __name__ == "__main__":
    main()
