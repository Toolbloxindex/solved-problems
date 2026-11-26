"""Replay the first-column classification and its exceptional rows."""
from math import comb


def multinomial_row(n):
    """Sum powers of 1 + q + q^2 by choosing linear and quadratic factors."""
    row = [0] * (2 * n - 1)
    for power in range(n):
        for twos in range(power + 1):
            for ones in range(power - twos + 1):
                row[2 * twos + ones] += comb(power, twos) * comb(power - twos, ones)
    return row


def check(max_n=256):
    row = [1]
    centers = 0
    for n in range(1, max_n + 1):
        if n <= 18 and row != multinomial_row(n):
            raise ArithmeticError(f"Independent expansion failed for n={n}")
        gaps = [b * b - a * c for a, b, c in zip(row, row[1:], row[2:])]
        centers += len(gaps)
        if min(row) <= 0 or all(g > 0 for g in gaps) != (n == 1 or n >= 6):
            raise ArithmeticError(f"Strict classification failed for n={n}")
        if gaps and 12 * gaps[0] != n * n * (n - 1) * (n - 5):
            raise ArithmeticError(f"Degree-one formula failed for n={n}")
        if n == 5 and gaps != [0, 150, 105, 201, 75, 45, 5]:
            raise ArithmeticError("Unexpected equality in row five")
        padded = [0, 0, *row, 0, 0]
        row = [a + b + c for a, b, c in zip(padded, padded[1:], padded[2:])]
        row[0] += 1
    print(f"Verified rows 1 through {max_n} and {centers} interior gaps.")


if __name__ == "__main__":
    check()
