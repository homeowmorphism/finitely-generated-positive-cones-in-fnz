#!/usr/bin/env python3
"""Independent exact arithmetic checks for the blueprint; NOT a Lean proof.

The six-state group identities are checked exhaustively by free-word reduction.
The d-dependent checks are regression tests for 1 <= d <= --max-d, not proofs
for all d. The standard library is the only dependency.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from math import gcd
from pathlib import Path
from typing import Iterable


def reduce_word(letters: Iterable[int]) -> tuple[int, ...]:
    stack: list[int] = []
    for a in letters:
        if a == 0:
            raise ValueError("Free-group letters must be nonzero signed integers")
        if stack and stack[-1] == -a:
            stack.pop()
        else:
            stack.append(a)
    return tuple(stack)


def inverse_word(w: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(-a for a in reversed(w))


@dataclass(frozen=True)
class D:
    """An element of F(x,y) x Z, in reduced-word coordinates."""
    word: tuple[int, ...] = ()
    z: int = 0

    def __mul__(self, other: D) -> D:
        return D(reduce_word(self.word + other.word), self.z + other.z)

    def inv(self) -> D:
        return D(inverse_word(self.word), -self.z)

    def __pow__(self, exponent: int) -> D:
        if exponent < 0:
            return self.inv() ** (-exponent)
        out = D()
        for _ in range(exponent):
            out = out * self
        return out


X, Y, Z = D((1,)), D((2,)), D((), 1)
ALPHA = (
    X,
    Y * X * Z**-1,
    X**-1 * Y * X * Z**-1,
    X**-1 * Y**-1 * X**-1 * Y * X,
    X**-1 * Y**-1 * Z**2,
    X**-1 * Y**-1 * X * Z**2,
)
C = Y**-1 * X**-1 * Y * X * Z**-1
BETA = (C, D(), D(), D(), D(), D())


def gamma_step(s: int, h: D, letter: int) -> tuple[int, D]:
    """Right action: a=1, b=2, inverse letters have negative signs."""
    if letter == 1:
        return (s + 2) % 6, h * ALPHA[s]
    if letter == 2:
        return (s - 1) % 6, h * BETA[s]
    if letter == -1:
        prior = (s - 2) % 6
        return prior, h * ALPHA[prior].inv()
    if letter == -2:
        prior = (s + 1) % 6
        return prior, h * BETA[prior].inv()
    raise ValueError("Expected a signed a or b letter")


def gamma_eval(word: Iterable[int], state: int = 0) -> tuple[int, D]:
    h = D()
    for letter in word:
        state, h = gamma_step(state, h, letter)
    return state, h


def check_fixed_certificate() -> dict[str, int | bool]:
    checks = 0
    for s in range(6):
        rhs = BETA[s] * ALPHA[(s - 1) % 6] * ALPHA[(s + 1) % 6] * BETA[(s + 3) % 6]
        assert ALPHA[s] == rhs, (s, ALPHA[s], rhs)
        checks += 1
        assert gamma_eval((2, 1, 1, 2, -1), s) == (s, D())
        checks += 1
        for letter in (1, 2, -1, -2):
            assert gamma_eval((letter, -letter), s) == (s, D())
            checks += 1
        r = (s + 2) % 6
        assert gamma_eval((-2,) * s + (1,) + (2,) * r) == (0, ALPHA[s])
        checks += 1
    for word, result in [
        ((1, 2, 2), X),
        ((1, 1, 2, 2, 1, 1), Y),
        ((1, 1, 1), Z),
        ((2,) * 6, C),
    ]:
        assert gamma_eval(word) == (0, result)
        checks += 1
    assert ALPHA[0] * ALPHA[2] * ALPHA[4] == Z
    assert ALPHA[0] * ALPHA[2]**2 * ALPHA[4] == Y
    checks += 2
    return {"passed": True, "exact_assertions": checks, "states_exhausted": 6}


def sigma_x(i: int, d: int) -> int:
    if i > 0 and i % 2 == 0:
        return i - 1
    if i % 2 == 1 and i + 1 < d:
        return i + 1
    return i


def sigma_y(i: int, d: int) -> int:
    if i % 2 == 1:
        return i - 1
    if i + 1 < d:
        return i + 1
    return i


def relabel(j: int, d: int) -> int:
    return 2 * j if 2 * j < d else 2 * (d - j) - 1


def basis_step(s: int, word: tuple[int, ...], letter: int, d: int) -> tuple[int, tuple[int, ...]]:
    """Weighted action for free generators X=1 and U=2.
    Basis labels 1,...,d denote the free generators e_0,...,e_{d-1} of E_d = FreeGroup(Fin d + Unit),
    i.e. the values lambda_d(a_j); d+1 denotes e_*, the value lambda_d(c_d).
    """
    if letter == 1:
        return (-s) % d, reduce_word(word + (s + 1,))
    if letter == -1:
        prior = (-s) % d
        return prior, reduce_word(word + (-(prior + 1),))
    if letter == 2:
        return (s + 1) % d, reduce_word(word + ((d + 1,) if s == d - 1 else ()))
    if letter == -2:
        prior = (s - 1) % d
        return prior, reduce_word(word + ((-(d + 1),) if prior == d - 1 else ()))
    raise ValueError("Expected a signed X or U letter")


def basis_eval(letters: Iterable[int], d: int, s: int = 0) -> tuple[int, tuple[int, ...]]:
    word: tuple[int, ...] = ()
    for letter in letters:
        s, word = basis_step(s, word, letter, d)
    return s, word


def check_family(max_d: int) -> dict[str, int | bool]:
    checks = 0
    for d in range(1, max_d + 1):
        assert sorted(relabel(j, d) for j in range(d)) == list(range(d))
        checks += 1
        for j in range(d):
            rx, ry = (-j) % d, (-j - 1) % d
            assert relabel(rx, d) == sigma_x(relabel(j, d), d)
            assert relabel(ry, d) == sigma_y(relabel(j, d), d)
            assert (-ry) % d == (j + 1) % d
            # g = y^-1 x^-1 y x, with reflections as letter actions.
            state = j
            for which in ('y', 'x', 'y', 'x'):
                state = (-state - (which == 'y')) % d
            assert state == (j + 2) % d
            checks += 4
            r = (-j) % d
            aj = (2,) * j + (1,) + (-2,) * r
            assert basis_eval(aj, d) == (0, (j + 1,))
            checks += 1
            for letter in (1, 2, -1, -2):
                assert basis_eval((letter, -letter), d, j) == (j, ())
                checks += 1
        orbit = {(2 * k) % d for k in range(d)}
        assert len(orbit) == d // gcd(2, d)
        assert (len(orbit) == d) == (d % 2 == 1)
        assert basis_eval((2,) * d, d) == (0, (d + 1,))
        checks += 3
        if d % 2 == 1:
            inv2 = (d + 1) // 2
            assert (2 * inv2) % d == 1 % d
            for j in range(d):
                assert (2 * ((inv2 * j) % d)) % d == j
                checks += 1
            checks += 1
    return {"passed": True, "min_d": 1, "max_d": max_d,
            "regression_assertions": checks, "uniform_proof": False}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: assertions must be enabled for verification")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-d', type=int, default=128)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.max_d < 1:
        parser.error('--max-d must be positive')
    result = {
        "status": "passed",
        "method": "integer arithmetic and reduced free-group words; not kernel checked",
        "fixed_six_state_certificate": check_fixed_certificate(),
        "parameterized_regression_tests": check_family(args.max_d),
        "not_checked": [
            "Lean elaboration or kernel checking",
            "the Dubrovina-Dubrovin/Navas positive-cone theorem",
            "the MMRT odd-rank obstruction",
            "universal statements in d by a formal proof",
            "derivations of identities inside the presented group Gamma2",
        ],
    }
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
