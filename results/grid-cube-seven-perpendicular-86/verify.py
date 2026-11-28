"""Replay the perpendicular seven-cube forest using only Python's standard library."""

import json
import sys
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from math import gcd
from pathlib import Path


SIDE = 7
TARGET = 87


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def pair_blockers(side, dimension):
    """The mask at [p][q] consists of the other grid points on the line pq."""
    points = list(product(range(side), repeat=dimension))
    number = {point: i for i, point in enumerate(points)}
    table = [[0] * len(points) for _ in points]
    for i, j in combinations(range(len(points)), 2):
        p, q = points[i], points[j]
        delta = tuple(b - a for a, b in zip(p, q))
        divisor = gcd(*delta)
        step = tuple(d // divisor for d in delta)
        # A nonzero coordinate of step bounds the parameter by side - 1.
        sites = (tuple(a + t * d for a, d in zip(p, step))
                 for t in range(1 - side, side) if t not in (0, divisor))
        table[i][j] = table[j][i] = sum(1 << number[r] for r in sites if r in number)
    return table


def blocked(points, table):
    out = 0
    for p, q in combinations(points, 2):
        out |= table[p][q]
    return out


class PlanarDomains:
    def __init__(self, side):
        self.side = side
        self.board = (1 << (side * side)) - 1
        self.blockers = pair_blockers(side, 2)
        self.rows = tuple(((1 << side) - 1) << (side * i) for i in range(side))
        self.columns = tuple(sum(1 << (side * i + j) for i in range(side))
                             for j in range(side))
        self.column_at = tuple(self.columns[p % side] for p in range(side * side))

    def search(self, size, allowed, required):
        """Enumerate exact completions by choosing the extra points in each row."""
        table = self.blockers
        chosen = list(indices(required))
        forbidden = blocked(chosen, table)
        if required & ~allowed or required & forbidden or len(chosen) > size:
            return ()
        unused_columns = self.board
        closed_columns = 0
        for p in chosen:
            column = self.column_at[p]
            closed_columns |= column & ~unused_columns
            unused_columns &= ~column
        available = allowed & ~(required | forbidden | closed_columns)
        rows = [(row, 2 - (row & required).bit_count()) for row in self.rows]
        rows = [(row, limit) for row, limit in rows if limit and row & available]
        rows.sort(key=lambda entry: (entry[0] & available).bit_count())
        result = []
        column_at = self.column_at

        def visit(offset, need, available, unused_columns, selected):
            if need == 0:
                result.append(selected)
                return
            if offset == len(rows):
                return
            limits = [min(limit, (row & available).bit_count())
                      for row, limit in rows[offset:]]
            rest = sum(limits[1:])
            row = rows[offset][0]
            choices = tuple(indices(row & available))
            if rest >= need:
                visit(offset + 1, need, available, unused_columns, selected)
            if rest + 1 >= need and limits[0]:
                for p in choices:
                    banned = 0
                    for q in chosen:
                        banned |= table[p][q]
                    column = column_at[p]
                    available_after = available & ~(banned | (column & ~unused_columns))
                    chosen.append(p)
                    visit(offset + 1, need - 1, available_after, unused_columns & ~column,
                          selected | (1 << p))
                    chosen.pop()
            if need >= 2 and rest + 2 >= need and limits[0] == 2:
                bans = {}
                for p in choices:
                    banned = 0
                    for q in chosen:
                        banned |= table[p][q]
                    bans[p] = banned
                for p, q in combinations(choices, 2):
                    if bans[p] & (1 << q):
                        continue
                    columns = column_at[p] | column_at[q]
                    banned = bans[p] | bans[q] | table[p][q] | (columns & ~unused_columns)
                    chosen.extend((p, q))
                    visit(offset + 1, need - 2, available & ~banned, unused_columns & ~columns,
                          selected | (1 << p) | (1 << q))
                    chosen.pop()
                    chosen.pop()

        visit(0, size - len(chosen), available, unused_columns, required)
        return tuple(sorted(result))

    def prepare_high_banks(self):
        self.high = {size: self.search(size, self.board, 0) for size in (14, 13)}
        self.inverted = {}
        for size, bank in self.high.items():
            containing = [[] for _ in range(self.side ** 2)]
            for cap in bank:
                for p in indices(cap):
                    containing[p].append(cap)
            self.inverted[size] = containing

    @lru_cache(maxsize=4096)
    def containing(self, size, required):
        if not required:
            return self.high[size]
        anchor = (required & -required).bit_length() - 1
        return tuple(cap for cap in self.inverted[size][anchor] if cap & required == required)

    @lru_cache(maxsize=32768)
    def domain(self, size, allowed, required):
        if size in self.high:
            return tuple(cap for cap in self.containing(size, required) if cap & allowed == cap)
        return self.search(size, allowed, required)


class Cube:
    def __init__(self):
        self.points = tuple(product(range(SIDE), repeat=3))
        self.board = (1 << len(self.points)) - 1
        self.blockers = pair_blockers(SIDE, 3)
        self.slots = tuple(product(range(3), range(SIDE)))
        self.planes = {slot: tuple(i for i, p in enumerate(self.points) if p[slot[0]] == slot[1])
                       for slot in self.slots}
        self.plane_masks = {slot: sum(1 << i for i in plane) for slot, plane in self.planes.items()}
        self.site_planes = []
        for x, y, z in self.points:
            self.site_planes.append(((x, 1 << (SIDE * y + z)),
                                     (SIDE + y, 1 << (SIDE * x + z)),
                                     (2 * SIDE + z, 1 << (SIDE * x + y))))

    def embed(self, slot, cap):
        plane = self.planes[slot]
        return sum(1 << plane[i] for i in indices(cap))

    def project(self, mask):
        local = [0] * (3 * SIDE)
        for p in indices(mask):
            for slot, bit in self.site_planes[p]:
                local[slot] |= bit
        return local

    def available(self, fixed, slots):
        banned = blocked(tuple(indices(fixed)), self.blockers)
        if banned & fixed:
            return None
        for slot in slots:
            banned |= self.plane_masks[slot]
        return self.board & ~(fixed | banned)

    def axis_bound(self, fixed, allowed):
        # Taking either zero, one or two sites on a line is the best possible
        # if that coordinate direction is the only constraint.
        capacities = []
        for axis in range(3):
            counts = [0] * (SIDE * SIDE)
            for p in indices(fixed | allowed):
                flat = self.site_planes[p][axis][1].bit_length() - 1
                counts[flat] += 1
            capacities.append(sum(min(2, count) for count in counts))
        return min(capacities)

    def roots(self, full_bank):
        embeddings = {slot: {cap: self.embed(slot, cap) for cap in full_bank}
                      for slot in self.slots}
        for heights in combinations_with_replacement(range(4), 3):
            a, b, c = tuple(enumerate(heights))

            def buckets(left, right):
                intersection = self.plane_masks[left] & self.plane_masks[right]
                by_intersection = defaultdict(set)
                for cap, sites in embeddings[right].items():
                    by_intersection[sites & intersection].add(cap)
                return {cap: by_intersection[sites & intersection]
                        for cap, sites in embeddings[left].items()}

            ab, ac, bc = buckets(a, b), buckets(a, c), buckets(b, c)
            for aa in full_bank:
                for bb in ab[aa]:
                    for cc in ac[aa] & bc[bb]:
                        yield (heights, (aa, bb, cc)), (a, b, c), (
                            embeddings[a][aa] | embeddings[b][bb] | embeddings[c][cc]
                        )


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def totals(bounds):
    return [sum(bounds[j:j + SIDE]) for j in range(0, 3 * SIDE, SIDE)]


class Replay:
    def __init__(self):
        self.cube = Cube()
        self.domains = PlanarDomains(SIDE)
        self.domains.prepare_high_banks()
        self.root_counts = Counter()
        self.leaf_counts = Counter()

    def local(self, fixed, allowed):
        return tuple(zip(self.cube.project(fixed | allowed), self.cube.project(fixed)))

    def refine(self, bounds, local, sizes):
        for size in sizes:
            for i, bound in enumerate(bounds):
                if bound == size and not self.domains.domain(size, *local[i]):
                    bounds[i] -= 1

    def high_bounds(self, local, bounds):
        for i, (allowed, required) in enumerate(local):
            for size in (14, 13):
                if bounds[i] == size and not self.domains.domain(size, allowed, required):
                    bounds[i] = size - 1

    def root_bounds(self, fixed, slots):
        allowed = self.cube.available(fixed, slots)
        if allowed is None or self.cube.axis_bound(fixed, allowed) < TARGET:
            return None
        local = self.local(fixed, allowed)
        bounds = [14] * (SIDE * 3)
        self.high_bounds(local, bounds)
        bound = min(totals(bounds))
        if bound < TARGET:
            return None
        self.root_counts["high"] += 1
        for size in (12, 11):
            self.refine(bounds, local, (size,))
            bound = min(totals(bounds))
            if bound < TARGET:
                return None
            self.root_counts[size] += 1
        return bounds, local

    def check_record(self, slots, fixed, bounds, local, record):
        require(record["ceilings"] == bounds and record["sums"] == totals(bounds),
                "incorrect root ceilings")
        plane = tuple(record["first_plane"])
        require(plane in self.cube.planes and plane not in slots, "invalid branch plane")
        axis, height = plane
        index = SIDE * axis + height
        high = bounds[index]
        low = max(0, TARGET - (totals(bounds)[axis] - high))
        expected = [cap for size in range(low, high + 1)
                    for cap in self.domains.domain(size, *local[index])]
        listed = [cap for cap, _ in record["leaves"]]
        require(listed == expected, f"incomplete or invalid branch cover for {plane}: "
                                   f"missing {sorted(set(expected) - set(listed))}, "
                                   f"expected {len(expected)}, listed {len(listed)}")
        for cap, (rule, printed) in record["leaves"]:
            larger = fixed | self.cube.embed(plane, cap)
            allowed = self.cube.available(larger, (*slots, plane))
            require(allowed is not None, "recorded leaf has inconsistent fixed points")
            bound = self.cube.axis_bound(larger, allowed)
            if bound >= TARGET:
                require(rule == "layer_ceilings", "invalid layer-ceiling leaf tag")
                reduced = self.local(larger, allowed)
                updated = bounds.copy()
                updated[index] = cap.bit_count()
                self.high_bounds(reduced, updated)
                for size in (12, 11, 10):
                    if min(totals(updated)) < TARGET:
                        break
                    self.refine(updated, reduced, (size,))
                bound = min(totals(updated))
            else:
                require(rule == "axis_lines", "invalid axis-line leaf tag")
            require(bound == printed and bound < TARGET, "leaf does not exclude size 87")
            self.leaf_counts[rule] += 1

    def run(self, records, pilot):
        supplied = {}
        for record in records:
            key = tuple(record["heights"]), tuple(record["masks"])
            require(key not in supplied, "duplicate root")
            supplied[key] = record
        full_bank = self.domains.high[14]
        if pilot:
            roots = []
            for (heights, masks), record in supplied.items():
                require(heights == tuple(sorted(heights)) and len(heights) == len(masks) == 3
                        and all(0 <= h <= 3 for h in heights) and all(m in full_bank for m in masks),
                        "invalid pilot root")
                slots = tuple(enumerate(heights))
                fixed = 0
                for slot, mask in zip(slots, masks):
                    fixed |= self.cube.embed(slot, mask)
                require(all(fixed & self.cube.plane_masks[s] == self.cube.embed(s, m)
                            for s, m in zip(slots, masks)), "inconsistent pilot planes")
                roots.append(((heights, masks), slots, fixed))
        else:
            roots = self.cube.roots(full_bank)

        for key, slots, fixed in roots:
            self.root_counts["visited"] += 1
            result = self.root_bounds(fixed, slots)
            if result is None:
                continue
            require(key in supplied, f"missing residual root {key}")
            self.check_record(slots, fixed, *result, supplied.pop(key))
        require(not supplied, "unused residual root")
        print(f"Full/near-full planar banks: {len(full_bank)}, {len(self.domains.high[13])}")
        print(f"Roots: {dict(self.root_counts)}")
        print(f"Leaves: {dict(self.leaf_counts)}")


def main():
    args = sys.argv[1:]
    if len(args) == 2 and args[0] == "--pilot":
        path, pilot = Path(args[1]), True
    elif not args:
        path, pilot = Path(__file__).with_name("forest.json"), False
    else:
        raise ValueError("use verify.py or verify.py --pilot FILE")
    Replay().run(json.loads(path.read_text(encoding="ascii"))["records"], pilot)
    print("PILOT PASS" if pilot else "PASS")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, IndexError) as error:
        sys.exit(f"FAIL: {error}")
