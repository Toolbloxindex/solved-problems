#!/usr/bin/env python3
"""Check the Lean table against graph moves with unreduced leaf and P2 counts."""
from functools import cache, reduce
from itertools import product
from operator import xor
from pathlib import Path
import re


def members(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def mex(options):
    options = set(options)
    return next(i for i in range(len(options)+1) if i not in options)


def graph(n, edges):
    rows = [0] * n
    for i, j in edges:
        rows[i] |= 1 << j
        rows[j] |= 1 << i
    return tuple(rows)


def cap(n, b):
    return n if n < b else b + (n-b) % 4


def full(rows):
    return (1 << len(rows)) - 1


def bit_graph(n, mask):
    pairs = ((i, j) for i in range(n) for j in range(i))
    return graph(n, (p for b, p in enumerate(pairs) if mask >> b & 1))


def path(n):
    return graph(n, ((i, i+1) for i in range(n-1)))


def cycle(n):
    return graph(n, ((i, (i+1)%n) for i in range(n)))


def composition(parts, joined=False):
    rows, offset = [], 0
    for part in parts:
        rows.extend(row << offset for row in part)
        offset += len(part)
    if joined:
        offset = 0
        for part in parts:
            block = full(part) << offset
            cross = full(rows) ^ block
            for i in range(offset, offset+len(part)):
                rows[i] |= cross
            offset += len(part)
    return tuple(rows)


def disjoint(*parts):
    return composition(parts)


def join(*parts):
    return composition(parts, joined=True)


def make_core():
    one = path(1)
    fork = join(bit_graph(6, 2353), one)
    end = join(bit_graph(6, 1110), one)
    modules = (
        bit_graph(5, 20),
        disjoint(join(disjoint(one, bit_graph(4, 3), path(3)), one), cycle(16)),
        disjoint(fork, cycle(18)),
        disjoint(join(disjoint(one, cycle(6)), bit_graph(4, 3)), cycle(35)),
        disjoint(join(bit_graph(6, 1174), one), join(cycle(35), cycle(18), cycle(16))),
        disjoint(fork, end, end),
        disjoint(cycle(78), path(3)),
    )
    starts = tuple(sum(len(s) for s in modules[:i]) for i in range(len(modules)))
    return join(*modules), starts


def remove(rows, board, v):
    return board & ~(rows[v] | 1 << v)


def components(rows, board):
    queue = board
    while queue:
        wave = queue & -queue
        landed = 0
        while wave:
            landed |= wave
            frontier = 0
            for i in members(wave):
                frontier |= rows[i]
            wave = frontier & board & ~landed
        yield landed
        queue ^= landed


def run_sizes(board):
    while board:
        low = board & -board
        board //= low
        run = (board ^ (board+1)).bit_length()-1
        yield run
        board >>= run


@cache
def path_sg(n):
    rows = path(n)
    return mex(reduce(xor, map(path_sg, run_sizes(remove(rows, full(rows), i))), 0)
               for i in range(n))


def core_solver(rows):
    complement = tuple(full(rows) ^ (row | 1 << i) for i, row in enumerate(rows))

    @cache
    def sg(board):
        return mex(options(board))

    @cache
    def options(board):
        if not board:
            return frozenset()
        pieces = tuple(components(rows, board))
        if len(pieces) > 1:
            value = reduce(xor, map(sg, pieces), 0)
            return frozenset(value ^ sg(part) ^ child
                             for part in pieces for child in options(part))
        co_pieces = tuple(components(complement, board))
        if len(co_pieces) > 1:
            return frozenset().union(*(options(part) for part in co_pieces))
        degrees = [(rows[i] & board).bit_count() for i in members(board)]
        if max(degrees) <= 2:
            n = board.bit_count()
            if min(degrees) == 2:
                return frozenset({path_sg(n-3)})
            strip = path(n)
            return frozenset(
                reduce(xor, map(path_sg, run_sizes(remove(strip, full(strip), i))), 0)
                for i in range(n)
            )
        return frozenset(sg(remove(rows, board, i)) for i in members(board))

    return sg, options


def arm_moves(n):
    rows = path(n)
    transitions = []
    for i in range(n):
        left = remove(rows, full(rows), i)
        runs = tuple(run_sizes(left))
        # The attached component must include label zero and the hub must survive.
        retained = runs[0] if i and left & 1 else 0
        detached = runs[1:] if retained else runs
        transitions.append((not i, retained, reduce(xor, map(path_sg, detached), 0)))
    return tuple(transitions)


def solve():
    rows, marks = make_core()
    core_sg, core_options = core_solver(rows)
    mark_mask = sum(1 << i for i in marks)
    slots = (full(rows), *(remove(rows, full(rows), i) for i in marks))
    arms = tuple(arm_moves(n) for n in (1,2,3,5))
    sizes = (1,2,3,5)
    raw = tuple(map(path_sg, sizes))
    cut = tuple(path_sg(n-1) for n in sizes)
    erased = tuple(map(core_sg, slots))
    after_hub = tuple(core_sg(board & mark_mask) for board in slots)
    near = tuple(frozenset(core_sg(remove(rows, board, i))
                           for i in members(board & ~mark_mask)) for board in slots)
    assert [len(rows)+1, marks, tuple(map(int.bit_count, slots))] == [
        280, (0,5,30,55,101,177,198), (279,4,23,22,41,72,18,78)]
    assert after_hub == (1,0,0,0,0,0,0,0)
    assert tuple(sum(1 << k for k in s) for s in near) == (15,7,45,71,132,227,247,1271)
    assert erased == (4,3,1,3,0,2,3,3)
    assert all(core_options(s) == near[i] for i, s in enumerate(slots) if i)
    print('module orders', tuple((marks+(len(rows),))[i+1]-marks[i] for i in range(7)), flush=True)
    print('surviving core sizes', tuple(map(int.bit_count, slots)), flush=True)
    print('hub nimbers', after_hub, 'erased nimbers', erased, flush=True)
    print('near and seven menus', [sorted(s) for s in near], flush=True)
    print('literal arm transitions', dict(zip(sizes, arms)), flush=True)

    @cache
    def sg(h, counts):
        return mex(options(h, counts))

    def options(h, counts):
        parity = [i for i, n in enumerate(counts) if n & 1]
        detached = reduce(xor, (raw[i] for i in parity), 0)
        after_cut = reduce(xor, (cut[i] for i in parity), 0)
        yield after_hub[h] ^ after_cut
        yield from (k ^ detached for k in near[h])
        if h == 0:
            yield from (sg(j, counts) for j in range(1, 8))
        for i, n in enumerate(counts):
            if n:
                for kills_hub, residual, extra in arms[i]:
                    if kills_hub:
                        yield erased[h] ^ detached ^ raw[i] ^ extra
                        continue
                    next_counts = list(counts)
                    next_counts[i] -= 1
                    if residual:
                        next_counts[sizes.index(residual)] += 1
                    yield sg(h, tuple(next_counts)) ^ extra

    lean = Path(__file__).with_name('PeriodFourTable.lean')
    rows_table = {(int(h), int(m)): tuple(map(int, values.split(',')))
                  for h, m, values in re.findall(r'\| (\d), (\d) => \[([0-9,]+)\]', lean.read_text())}
    assert len(rows_table) == 56

    def profile(h, x, c, z):
        gap = cap(abs(c-x), 3) * (1 if c>=x else -1)
        return rows_table[h, cap(min(x,c), 3)][2*(gap+6)+z]

    def claimed_options(h, x, c, z):
        detached = path_sg(5)*(x%2) ^ path_sg(3)*(c%2) ^ z
        result = {k ^ detached for k in near[h]}
        result |= {(c%2)^int(h==0), erased[h]^detached^1}
        if h==0:
            result.update(profile(j,x,c,z) for j in range(1,8))
        if x:
            result |= {profile(h,x-1,c,0)^1, profile(h,x-1,c,1)^1, profile(h,x-1,c+1,z)}
        if c:
            result |= {erased[h]^detached^3,profile(h,x,c-1,0),profile(h,x,c-1,1)}
        return result

    for h, m, d, z in product(range(8), range(8), range(-8,9), range(2)):
        x,c = m+max(0,-d), m+max(0,d)
        counts = (2-z, 0, c, x)
        observed = set(options(h, counts))
        assert observed == claimed_options(h, x, c, z), (h,x,c,z,observed,claimed_options(h,x,c,z))
        assert sg(h, counts) == profile(h,x,c,z), (h,x,c,z,sg(h,counts),profile(h,x,c,z))
    print('2176 detailed cells matched complete options and values', sg.cache_info(), flush=True)

    first = [(x, sorted(set(options(0,(2,0,3,x)))), sg(0,(2,0,3,x))) for x in (0,1,5,7,9,11)]
    print('parent with 2 leaves and 3 P3s', first, flush=True)
    for counts in ((1,0,0,0), (2,0,0,0),(1,0,1,0),(2,0,0,1),(1,0,3,5),(2,0,3,7)):
        for h in range(8):
            three = (counts[0]+2,) + counts[1:]
            shifted = (counts[0], counts[1]+1) + counts[2:]
            assert sg(h, counts) == sg(h, three)
            assert sg(h, counts)^1 == sg(h, shifted)
    print('96 extra raw leaf-pair and rooted-P2 shift checks passed', flush=True)


if __name__ == '__main__':
    solve()
