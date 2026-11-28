"""Compare a row-and-gap construction to the rank formula and the source slice."""
from collections import Counter
from itertools import combinations_with_replacement, product


def geometric_chains(m):
    for t in range(m // 2):
        j = m - 1 - t
        chain = [(t, k) for k in range(t, j + 1)]
        for s in range(1, t + 2):
            chain.append((t + s, j + s - 1))
            if s <= t:
                chain.append((t + s, j + s))
        yield chain


def saved_chains(m):
    for t in range(m // 2):
        chain = []
        for r in range(2 * t, 2 * t + m + 1):
            i = t + max(0, (r + 2 - m) // 2)
            chain.append((i, r - i))
        yield chain


def weight(m, pair):
    i, j = pair
    return tuple(int(h == i) + int(h == j) for h in range(m))


def suffixes(point):
    total = 0
    rows = []
    for x in reversed(point):
        total += x
        rows.append(total)
    return tuple(reversed(rows))


def check_steps(chains):
    for chain in chains:
        rows = list(map(suffixes, chain))
        for before, after in zip(rows, rows[1:]):
            delta = [y - x for x, y in zip(before, after)]
            assert delta.count(1) == 1 and delta.count(0) == len(delta) - 1


def audit(m):
    geometric = list(geometric_chains(m))
    assert geometric == list(saved_chains(m))
    actual = Counter(pair for chain in geometric for pair in chain)
    expected = Counter(combinations_with_replacement(range(m), 2))
    assert actual == expected and len(geometric) == m // 2
    assert all(len(chain) == m + 1 for chain in geometric)
    for i, j in expected:
        t = min(i, m // 2 - 1 - (j - i) // 2)
        assert geometric[t][i + j - 2 * t] == (i, j)
    chains = [[weight(m, pair) for pair in chain] for chain in geometric]
    check_steps(chains)
    reflected = [[tuple(m - x for x in point) for point in reversed(chain)]
                 for chain in chains]
    check_steps(reflected)
    if m <= 6:
        for cut, ribbons in ((2, chains), (m*m - 2, reflected)):
            source = Counter(x for x in product(range(m + 1), repeat=m) if sum(x) == cut)
            found = Counter(x for ribbon in ribbons for x in ribbon)
            assert found == source
    hist = Counter(i + j for i, j in expected)
    assert hist == Counter(2*t + k for t in range(m//2) for k in range(m+1))
    return geometric


if __name__ == "__main__":
    for m in range(2, 66, 2):
        audit(m)
    print("a=7:", *audit(6), sep="\n")
    print("Checked a=3,5,...,65, with literal Box enumeration at a=3,5,7.")
    print("PASS")
