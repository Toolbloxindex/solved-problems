"""Exact arithmetic for the rank-31 positive-weight counterexample."""
from itertools import combinations, permutations
from math import comb


def insert_maximum(length, counts):
    result = [0] * (len(counts) + 1)
    for descents, count in enumerate(counts):
        result[descents] += (descents + 1) * count
        result[descents + 1] += (length - descents) * count
    if result[-1] == 0:
        result.pop()
    return result


def fixed_deletions(rank, deleted):
    counts, length = [1], 0
    for label in range(1, rank + 1):
        if label not in deleted:
            counts = insert_maximum(length, counts)
            length += 1
        counts = insert_maximum(length, counts)
        length += 2
    return counts


def literal_words(rank, deleted):
    letters = [2 * j for j in range(1, rank + 1) for _ in range(2)]
    letters.extend(2 * j - 1 for j in range(1, rank + 1) if j not in deleted)
    counts = [0] * (2 * rank - len(deleted))
    for word in set(permutations(letters)):
        if all(
            all(element > j for element in word[word.index(j) + 1 : word.index(j, word.index(j) + 1)])
            for j in range(2, 2 * rank + 1, 2)
        ):
            counts[sum(a > b for a, b in zip(word, word[1:]))] += 1
    return counts


def equal_weight(rank, deletions):
    # Coefficient of u^deletions in h_rank(j*(j+u): 1 <= j <= n).
    degree = 2 * rank - deletions - 1
    length = 3 * rank - deletions
    h = [[0] * (deletions + 1) for _ in range(rank + 1)]
    h[0][0] = 1
    diagonal = [0]
    for n in range(1, degree + 2):
        for r in range(1, rank + 1):
            for i in range(min(r, deletions) + 1):
                h[r][i] += n * n * h[r - 1][i]
                if i:
                    h[r][i] += n * h[r - 1][i - 1]
        diagonal.append(h[rank][deletions])
    return [
        sum((-1)**j * comb(length + 1, j) * diagonal[m - j] for j in range(m))
        for m in range(1, degree + 2)
    ]


def laguerre(poly, point):
    value, first, half_second = [
        sum(c * comb(j, i) * point ** (j - i) for j, c in enumerate(poly) if j >= i)
        for i in range(3)
    ]
    return first**2 - 2 * value * half_second


def main():
    for rank in range(1, 4):
        for deletions in range(rank + 1):
            rows = []
            for chosen in combinations(range(1, rank + 1), deletions):
                row = fixed_deletions(rank, chosen)
                assert row == literal_words(rank, chosen)
                rows.append(row)
            assert equal_weight(rank, deletions) == list(map(sum, zip(*rows, strict=True)))
    print("Literal words, gap insertion and source Jacobi–Stirling coefficients agree through rank 3.")

    rank = 31
    e = fixed_deletions(rank, range(1, 5))
    f = fixed_deletions(rank, range(28, 32))
    a = equal_weight(rank, 4)
    # Independent reconstruction of the full equal-weight sum from deletion sets.
    direct = [0] * (2 * rank - 4)
    for chosen in combinations(range(1, rank + 1), 4):
        for j, count in enumerate(fixed_deletions(rank, chosen)):
            direct[j] += count
    assert a == direct and a[0] == comb(rank, 4) == 31465
    assert len(a) == len(e) == len(f) == 58
    assert all(c > 0 for row in (a, e, f) for c in row)

    p = [left + 900 * right for left, right in zip(e, f, strict=True)]
    q = [base + 10**6 * extra for base, extra in zip(a, p, strict=True)]
    assert p[0] == 901 and q[0] == 901031465
    for label, row in (("two-term", p), ("strictly positive", q)):
        difference = laguerre(row, -23)
        assert difference < 0
        print(f"{label} Laguerre difference at -23 = {difference}")
    print("PASS")


if __name__ == "__main__":
    main()
