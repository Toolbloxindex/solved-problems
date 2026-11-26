"""Direct finite checks of the comparison with Graffiti.pc 392a."""

import argparse
from functools import cache
from itertools import combinations
from pathlib import Path


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def invariants(order, edges):
    neighbors = [0] * order
    for x, y in edges:
        neighbors[x] |= 1 << y
        neighbors[y] |= 1 << x
    degrees = [row.bit_count() for row in neighbors]
    universe = (1 << order) - 1

    def select(predicate):
        return sum(1 << x for x in range(order) if predicate(x))

    minimum_degree = min(degrees)
    minimum = select(lambda x: degrees[x] == minimum_degree)
    two = select(lambda x: degrees[x] == 2)
    exceptional = select(lambda x: (neighbors[x] & two).bit_count() == 1)
    forced = select(lambda x: degrees[x] < 2)
    high = select(lambda x: degrees[x] >= 3)

    @cache
    def matching(available):
        if not available:
            return 0
        x = next(vertices(available))
        rest = available ^ (1 << x)
        best = matching(rest)
        for y in vertices(neighbors[x] & rest):
            best = max(best, 1 + matching(rest ^ (1 << y)))
        return best

    def minimum_two_dominating():
        for size in range(order - forced.bit_count() + 1):
            for chosen in combinations(vertices(universe ^ forced), size):
                subset = forced | sum(1 << x for x in chosen)
                if all((neighbors[y] & subset).bit_count() >= 2 for y in vertices(universe ^ subset)):
                    return size + forced.bit_count()
        raise AssertionError("The full vertex set always 2-dominates.")

    bound_b = matching(universe ^ minimum) + minimum.bit_count() + exceptional.bit_count()
    bound_a = matching(high) + order - high.bit_count()
    return minimum_two_dominating(), bound_b, bound_a


def subdivided_clique(t):
    edges = []
    middle = t
    for x, y in combinations(range(t), 2):
        edges.extend([(x, middle), (middle, y)])
        middle += 1
    edges.append((0, middle))
    return middle + 1, edges


def graph6(line):
    """Read one short-form graph6 record (orders up to 62)."""
    data = line.strip().encode("ascii")
    n = data[0] - 63
    if not 0 <= n < 63 or len(data) != 1 + (n * (n - 1) // 2 + 5) // 6:
        raise ValueError("Expected a short-form graph6 record.")
    pairs = ((x, y) for y in range(n) for x in range(y))
    edges = [(x, y) for i, (x, y) in enumerate(pairs)
             if (data[1 + i // 6] - 63) & (1 << (5 - i % 6))]
    return n, edges


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", type=Path, help="McKay's connected order-eight graph6 file")
    args = parser.parse_args()
    for t in range(4, 7):
        values = invariants(*subdivided_clique(t))
        predicted = t + 1, t + 1, t * (t - 1) // 2 + 1
        assert values == predicted, (t, values, predicted)
        print(f"K{t} comparison (actual, 392b, 392a): {values}")
    for t in (4, 5):
        order, edges = subdivided_clique(t)
        block = range(order, order + 5)
        edges.extend(combinations(block, 2))
        edges.append((0, order))
        values = invariants(order + 5, edges)
        assert values == (t + 3, t + 3, t * (t - 1) // 2 + 4)
        # Pepper's bound adds the leaf to a minimum cover of its complement.
        nonleaves = [v for v in range(order + 5) if v != order - 1]
        core_edges = [(x, y) for x, y in edges if order - 1 not in (x, y)]
        def covers(chosen):
            return all(x in chosen or y in chosen for x, y in core_edges)
        cover_size = next(k for k in range(len(nonleaves) + 1)
                          if any(covers(set(C)) for C in combinations(nonleaves, k)))
        assert cover_size + 1 == t + 5
        print(f"K{t} with K5 block (actual, 392b, 392a, Pepper): {(*values, cover_size + 1)}")
    if args.census:
        count = tight = better = 0
        with args.census.open() as records:
            for record in records:
                n, edges = graph6(record)
                assert n == 8
                actual, bound_b, bound_a = invariants(n, edges)
                assert actual <= bound_b, record
                count += 1
                tight += actual == bound_b
                better += bound_b < bound_a
        assert (count, tight, better) == (11117, 759, 255)
        print(f"{count} graphs, {tight} equalities, {better} tighter bounds")


if __name__ == "__main__":
    main()
