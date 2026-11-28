"""Check certificates in the published order, without importing either solver."""

import argparse
import json
from collections import Counter
from itertools import accumulate, combinations, product
from math import comb, gcd
from pathlib import Path


def slice_bounds(a):
    coprime = [-1] + [c for c in range(1, (a - 1) ** 2 + 1) if gcd(a, c) == 1]
    return {(prior + 1, c) for prior, c in zip(coprime, coprime[1:])}


def suffix(x):
    return tuple(reversed(tuple(accumulate(reversed(x)))))


def small_partition_count():
    # Figure 12: the ten vertices of Box[2,2] at a=5.
    vertices = [suffix(x) for x in product(range(5), repeat=4) if sum(x) == 2]
    ribbons = []
    for subset in combinations(vertices, 5):
        chain = sorted(subset, key=sum)
        if all(sum(y) == sum(x) + 1 and all(a <= b for a, b in zip(x, y))
               for x, y in zip(chain, chain[1:])):
            ribbons.append(set(chain))
    return sum(first.isdisjoint(second) for first, second in combinations(ribbons, 2))


def check(a, lo, hi, ribbons):
    expected = {x for x in product(range(a), repeat=a - 1) if lo <= sum(x) <= hi}
    # Coefficients of (1-z^a)^(a-1)/(1-z)^(a-1), from bounded compositions.
    count = sum((-1)**j * comb(a - 1, j) * comb(s - a*j + a - 2, a - 2)
                for s in range(lo, hi + 1) for j in range(min(a - 1, s // a) + 1))
    assert len(expected) == count, ('slice size', lo, hi, len(expected), count)
    actual = Counter(x for ribbon in ribbons for x in ribbon)
    assert actual == Counter(expected), ('partition', actual - Counter(expected), Counter(expected) - actual)

    for ribbon in ribbons:
        assert len(ribbon) == a, ('length', ribbon)
        for x, z in zip(ribbon, ribbon[1:]):
            u, w = suffix(x), suffix(z)
            assert u != w and all(s <= t for s, t in zip(u, w)), ('order', x, z)
            interval = product(*(range(s, t + 1) for s, t in zip(u, w)))
            middle = set(interval) - {u, w}
            assert not middle, ('intermediate point', x, z, middle)
            # This also certifies ambient-lattice saturation, if read in Definition 10.1.
            assert sum(w) == sum(u) + 1, ('ambient cover', x, z)

    # Independent polynomial division: the ranks of the starts are forced.
    ranks = Counter(sum(suffix(x)) for x in expected)
    starts = Counter()
    for rank in range(max(ranks) + 1):
        starts[rank] = ranks[rank] - sum(starts[rank - offset] for offset in range(1, a))
        assert starts[rank] >= 0
    assert starts == Counter(sum(suffix(ribbon[0])) for ribbon in ribbons), ('rank polynomial', starts)
    print(f'a={a} sums={lo}..{hi} points={len(expected)} ribbons={len(ribbons)} '
          f'covers={sum(len(row) - 1 for row in ribbons)}')


def main():
    if not __debug__:
        raise RuntimeError('Certificate checks require Python assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='*', type=Path)
    parser.add_argument('--complete', type=int)
    args = parser.parse_args()
    # Published a=3 specialization, including its sign-sensitive order.
    controls = [((0, 1), [[(0, 0), (1, 0), (0, 1)]]),
                ((2, 2), [[(2, 0), (1, 1), (0, 2)]]),
                ((3, 4), [[(2, 1), (1, 2), (2, 2)]])]
    for (lo, hi), ribbons in controls:
        check(3, lo, hi, ribbons)
    try:
        check(3, 0, 1, [list(reversed(controls[0][1][0]))])
    except AssertionError as error:
        assert error.args[0][0] == 'order'
    else:
        raise AssertionError('reversed ribbon accepted')
    assert small_partition_count() == 2
    print('a=5 sums=2..2: two partitions, as in Figure 12.')

    certified = set()
    for path in args.paths:
        data = json.loads(path.read_text())
        a, lo, hi = (data[k] for k in ('a', 'lo', 'hi'))
        assert (lo, hi) in slice_bounds(a)
        ribbons = [list(map(tuple, row)) for row in data['ribbons']]
        check(a, lo, hi, ribbons)
        certified.add((a, lo, hi))
        height = (a - 1) ** 2
        opposite = (height - hi, height - lo)
        if (lo, hi) != opposite:
            assert opposite in slice_bounds(a)
            reflected = [[tuple(a - 1 - n for n in x) for x in reversed(row)] for row in ribbons]
            check(a, *opposite, reflected)
            certified.add((a, *opposite))
    if args.complete is not None:
        assert {(lo, hi) for a, lo, hi in certified if a == args.complete} == slice_bounds(args.complete)
        print(f'All source slices at a={args.complete} certified.')


if __name__ == '__main__':
    main()
