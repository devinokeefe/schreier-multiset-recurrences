#!/usr/bin/env python3
"""Exact finite checks for the word model, maps and recurrence certificates.

Multisets are sorted tuples. Polynomials store coefficients in ascending degree,
with an empty tuple for zero. These bounded checks supplement the proofs.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Iterable

Word = tuple[int, ...]
Multiset = tuple[int, ...]
Poly = tuple[int | Fraction, ...]


def require(condition: bool, context: object) -> None:
    if not condition:
        raise AssertionError(context)


def cost(q: int, r: int, w: Word) -> int:
    """Word cost for positive q and a nonnegative margin r."""
    return len(w) + (sum(w) + r) // q


def encode(q: int, r: int, n: int, f: Multiset) -> Word:
    """Read all multiplicities above the cutoff and below the unique maximum n."""
    j = (len(f) - 1 + r) // q
    multiplicities = Counter(f)
    return tuple(multiplicities[x] for x in range(j + 1, n))


def decode(q: int, r: int, w: Word) -> Multiset:
    """Recover the multiset positions and append its unique maximum."""
    j = (sum(w) + r) // q
    return tuple(x for x, d in enumerate(w, j + 1) for _ in range(d)) + (len(w) + j + 1,)


@lru_cache(maxsize=None)
def candidates(n: int) -> tuple[Multiset, ...]:
    """Enumerate multiplicities of the lower positions for a positive maximum n."""
    return tuple(tuple(x for x, d in enumerate(ds, 1) for _ in range(d)) + (n,)
                 for ds in product(range(3), repeat=n - 1))


@lru_cache(maxsize=None)
def family(q: int, r: int, n: int) -> frozenset[Multiset]:
    return frozenset(f for f in candidates(n) if len(f) + r <= q * f[0])


@lru_cache(maxsize=None)
def words_of_length(length: int) -> tuple[Word, ...]:
    return tuple(product(range(3), repeat=length))


def terminal(q: int, r: int, w: Word) -> Word:
    return tuple(q + d for d in w) + (2 * q - 1 - (sum(w) + r) % q,)


@lru_cache(maxsize=None)
def terminal_compositions(q: int, total: int) -> frozenset[Word]:
    """Enumerate compositions with interior parts q..q+2 and a final part q..2q-1."""
    result = {(total,)} if q <= total <= 2 * q - 1 else set()
    for first in (q, q + 1, q + 2):
        if total >= first + q:
            result.update((first,) + p for p in terminal_compositions(q, total - first))
    return frozenset(result)


def append_map(q: int, r: int, d: int, source_n: int, f: Multiset) -> Multiset:
    e = (r + d) // q
    require(f[-1] == source_n and f.count(source_n) == 1, ("maximum", f))
    return tuple(sorted(tuple(x + e for x in f[:-1]) +
                        (source_n + e,) * d + (source_n + e + 1,)))


def trim(p: Iterable[int | Fraction]) -> Poly:
    a = list(p)
    while a and a[-1] == 0:
        a.pop()
    return tuple(a)


def add(a: Poly, b: Poly) -> Poly:
    return trim((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b))))


def scale(a: Poly, k: int | Fraction) -> Poly:
    return trim(k * x for x in a)


def mul(a: Poly, b: Poly) -> Poly:
    out = [0] * max(0, len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def shift(a: Poly, n: int) -> Poly:
    return (0,) * n + a if a else ()


def remainder(a: Poly, b: Poly) -> Poly:
    require(bool(b), "polynomial division by zero")
    a = tuple(Fraction(x) for x in a)
    b = tuple(Fraction(x) for x in b)
    while a and len(a) >= len(b):
        a = add(a, scale(shift(b, len(a) - len(b)), -a[-1] / b[-1]))
    return a


def gcd_poly(a: Poly, b: Poly) -> Poly:
    while b:
        a, b = b, remainder(a, b)
    return scale(a, Fraction(1, 1) / a[-1])


D: dict[int, Poly] = {
    2: (1, -1, -2, -1),
    3: (1, -3, 3, -4, 2, -1),
    4: (1, -3, 3, -3, -2, -1),
}
H: Poly = (1, -1, 1)
NUM: dict[int, tuple[Poly, ...]] = {
    2: ((1, 1), (1,)),
    3: ((1,), H, mul(H, H)),
    4: ((1, 0, 2), (1, 0, 0, 1), (1, -1, 1, 1, 1), (1, -2, 3)),
}
INITIAL = {2: [1, 2, 4], 3: [1, 3, 6, 13, 31], 4: [1, 3, 8, 18, 41]}


def check_families(max_n: int, max_q: int) -> Counter[str]:
    """Compare independently enumerated families and words, including the explicit maps."""
    totals: Counter[str] = Counter()
    for q in range(1, max_q + 1):
        for r in range(q):
            for n in range(1, max_n + 1):
                fs = family(q, r, n)
                totals["literal_candidates"] += len(candidates(n))
                ws = {w for length in range(n) for w in words_of_length(length)
                      if cost(q, r, w) == n - 1}
                encoded = set()
                for f in fs:
                    w = encode(q, r, n, f)
                    require(cost(q, r, w) == n - 1, ("encode cost", q, r, n, f))
                    require(decode(q, r, w) == f, ("decode encode", q, r, n, f))
                    encoded.add(w)
                    totals["admissible_multisets"] += 1
                require(encoded == ws, ("exact word image", q, r, n))
                for w in ws:
                    f = decode(q, r, w)
                    require(f in fs and encode(q, r, n, f) == w, ("encode decode", q, r, n, w))
                    for d in range(3):
                        e, s = divmod(r + d, q)
                        expected = 1 + e + cost(q, s, w)
                        require(cost(q, r, (d,) + w) == expected, ("first digit", q, r, w, d))
                        require(cost(q, r, w + (d,)) == expected, ("last digit", q, r, w, d))
                        totals["digit_identities"] += 2
                if n <= min(6, max_n):
                    images = {terminal(q, r, w) for w in ws}
                    compositions = terminal_compositions(q, q * n + q - 1 - r)
                    require(images == compositions, ("terminal surjectivity", q, r, n))
                    for p in compositions:
                        w = tuple(t - q for t in p[:-1])
                        require(w in ws and terminal(q, r, w) == p, ("terminal inverse", q, r, n, p))
                        totals["terminal_compositions"] += 1
                for d in range(3):
                    e, s = divmod(r + d, q)
                    source_n = n - 1 - e
                    if source_n < 1:
                        continue
                    image = set()
                    for f in family(q, s, source_n):
                        g = append_map(q, r, d, source_n, f)
                        require(g in fs, ("append landing", q, r, n, d, f))
                        require(encode(q, r, n, g) == encode(q, s, source_n, f) + (d,),
                                ("append agreement", q, r, n, d, f))
                        image.add(g)
                        totals["transported_maps"] += 1
                        if q == 2:
                            if d == 0:
                                old = f[:-1] + (n,)
                            elif d == 1 and r == 0:
                                old = f + (n,)
                            elif d == 1:
                                old = tuple(x + 1 for x in f) + (n,)
                            else:
                                old = tuple(x + 1 for x in f) + (n - 1, n)
                            require(g == old, ("q2 named map", r, n, d, f))
                            totals["q2_named_maps"] += 1
                    require(image == {f for f in fs if f.count(n - 1) == d},
                            ("penultimate partition", q, r, n, d))
            require(len(family(q, r, 1)) == 1, ("n1", q, r))
            if max_n >= 2:
                require(len(family(q, r, 2)) == min(3, q - r), ("n2", q, r))
            for n in range(1, max_n + 1):
                require(encode(q, r, n, (n,)) == (0,) * (n - 1), ("zero slots", q, r, n))
    require(terminal(4, 0, ()) == (7,), "q4 terminal alphabet")
    require(encode(4, 0, 4, (2, 2, 4)) == (0, 2, 0), "retained zero example")
    require({terminal(3, 0, encode(3, 0, 2, f)) for f in family(3, 0, 2)} ==
            {(3, 5), (4, 4), (5, 3)}, "q3 example")
    return totals


def check_polynomials() -> Counter[str]:
    """Check the residue identities and coprimality of each reduced generating function."""
    totals: Counter[str] = Counter()
    for q, ns in NUM.items():
        for r, numerator in enumerate(ns):
            lhs = numerator
            for d in range(3):
                e, s = divmod(r + d, q)
                lhs = add(lhs, scale(shift(ns[s], 1 + e), -1))
            require(lhs == D[q], ("polynomial certificate", q, r, lhs))
            totals["polynomial_rows"] += 1
        require(gcd_poly(D[q], ns[0]) == (1,), ("reduced fraction", q))
    require(scale(D[4], 4) == add(mul(NUM[4][0], (8, -5, -4, -2)), (-4, -7)),
            "q4 Euclidean identity")
    require(sum(c * (-1) ** i for i, c in enumerate(D[2])) == 1, "q2 coprimality")
    require(1 + 2 * Fraction(-4, 7) ** 2 == Fraction(81, 49), "q4 coprimality")
    return totals


def check_sequences(max_n: int, max_q: int, coefficients: int) -> Counter[str]:
    """Compare residue counts, composition counts and rational-series coefficients."""
    totals: Counter[str] = Counter()
    for q in range(1, max_q + 1):
        counts = [[0] * coefficients for _ in range(q)]
        for N in range(coefficients):
            for r in range(q):
                value = int(N == 0)
                for d in range(3):
                    e, s = divmod(r + d, q)
                    delay = 1 + e
                    if delay <= N:
                        value += counts[s][N - delay]
                counts[r][N] = value
        parent = [0] * (q * coefficients)
        parent[0] = 1
        for k in range(1, len(parent)):
            parent[k] = sum(parent[k - d] for d in (q, q + 1, q + 2) if d <= k)
        for r in range(q):
            for N in range(coefficients):
                upper = q * (N + 1) - 1 - r
                expected = sum(parent[k] for k in range(max(0, upper - q + 1), upper + 1))
                require(counts[r][N] == expected, ("parent coefficients", q, r, N))
                totals["parent_coefficient_comparisons"] += 1
                if N + 1 <= max_n:
                    require(counts[r][N] == len(family(q, r, N + 1)),
                            ("literal residue counts", q, r, N))
                    totals["literal_coefficient_comparisons"] += 1
                if q in D:
                    residual = sum(D[q][i] * counts[r][N - i]
                                   for i in range(min(N + 1, len(D[q]))))
                    numerator = NUM[q][r][N] if N < len(NUM[q][r]) else 0
                    require(residual == numerator, ("rational series", q, r, N))
                    totals["rational_coefficient_comparisons"] += 1
            if r == 0 and q in D:
                require(counts[0][:len(INITIAL[q])] == INITIAL[q], ("initial values", q))
                order = len(D[q]) - 1
                for N in range(order, coefficients):
                    require(counts[0][N] == -sum(D[q][i] * counts[0][N - i]
                                                for i in range(1, order + 1)),
                            ("target recurrence", q, N + 1))
                    totals["target_recurrences"] += 1
    return totals


def run(max_n: int, max_q: int, coefficients: int) -> dict[str, object]:
    totals = check_families(max_n, max_q)
    totals.update(check_polynomials())
    totals.update(check_sequences(max_n, max_q, coefficients))
    return {
        "status": "PASS",
        "bounds": {"q": max_q, "n": max_n, "coefficients": coefficients},
        "checks": dict(sorted(totals.items())),
        "minimal_orders": {str(q): len(denominator) - 1 for q, denominator in D.items()},
        "scope": "Finite diagnostics and exact polynomial arithmetic; not a Lean execution.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=10)
    parser.add_argument("--max-q", type=int, default=8)
    parser.add_argument("--coefficients", type=int, default=1000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    require(4 <= args.max_q <= 12 and 2 <= args.max_n <= 11 and args.coefficients >= max(6, args.max_n),
            "Use 4 <= max-q <= 12, 2 <= max-n <= 11, coefficients >= max(6,max-n).")
    result = json.dumps(run(args.max_n, args.max_q, args.coefficients), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result, encoding="utf-8", newline="\n")
    print(result, end="")


if __name__ == "__main__":
    main()
