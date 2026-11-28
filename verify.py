"""Exact, standard-library replay of three one-edge closures from Problem 6.6."""



def graph(ell, arms, centers, branches):
    neighbors = [set()]

    def child(v):
        w = len(neighbors)
        neighbors.append({v})
        neighbors[v].add(w)
        return w

    def spider(parent, count):
        center = child(parent)
        middle = []
        for _ in range(count):
            v = child(center)
            child(v)
            middle.append(v)
        return middle

    spider(0, ell)
    endpoints = None
    for _ in range(branches):
        hub = child(0)
        for _ in range(centers):
            middle = spider(hub, arms)
            if endpoints is None:
                endpoints = middle[:2]
    u, v = endpoints
    assert v not in neighbors[u] and len(neighbors[u] & neighbors[v]) == 1
    neighbors[u].add(v)
    neighbors[v].add(u)
    assert sum(map(len, neighbors)) == 2 * len(neighbors)
    reached = {0}
    todo = [0]
    while todo:
        for w in neighbors[todo.pop()] - reached:
            reached.add(w)
            todo.append(w)
    assert len(reached) == len(neighbors)
    return neighbors, u


def add(a, b):
    result = [0] * max(len(a), len(b))
    for p in (a, b):
        for i, c in enumerate(p):
            result[i] += c
    return result


def multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, c in enumerate(a):
        for j, d in enumerate(b):
            result[i + j] += c * d
    return result


def forest(neighbors, removed):
    seen = set(removed)

    def visit(v, parent):
        assert v not in seen, "expected a forest"
        seen.add(v)
        excluded, included = [1], [0, 1]
        for w in neighbors[v]:
            if w == parent or w in removed:
                continue
            no_w, yes_w = visit(w, v)
            excluded = multiply(excluded, add(no_w, yes_w))
            included = multiply(included, no_w)
        return excluded, included

    total = [1]
    for v in range(len(neighbors)):
        if v not in seen:
            total = multiply(total, add(*visit(v, None)))
    return total


def formula(x, ell, arms, centers, branches):
    edge = 1 + 2 * x
    free = edge ** arms
    star = free + x * (1 + x) ** arms
    loss = x ** 2 * edge ** (arms - 2)
    hubs_out = star ** centers
    hubs_in = x * free ** centers
    marked_out = (star - loss) * star ** (centers - 1)
    marked_in = x * (free - loss) * free ** (centers - 1)
    base_free = edge ** ell
    base_star = base_free + x * (1 + x) ** ell
    return (base_star * (hubs_out + hubs_in) ** (branches - 1)
            * (marked_out + marked_in)
            + x * base_free * hubs_out ** (branches - 1) * marked_out)


def verify(params, expected):
    neighbors, u = graph(*params)
    count = len(neighbors)
    coefficients = add(forest(neighbors, {u}),
                       [0] + forest(neighbors, neighbors[u] | {u}))
    degree = len(coefficients) - 1
    assert coefficients[:3] == [1, count, count * (count - 1) // 2 - count]

    # Both polynomials have degree at most the vertex count. Equality at these
    # distinct integers proves identity, using a second counting method.
    for x in range(count + 1):
        value = 0
        for c in reversed(coefficients):
            value = value * x + c
        assert value == formula(x, *params)

    peak = coefficients.index(max(coefficients))
    assert all(coefficients[i] < coefficients[i + 1] for i in range(peak))
    assert all(coefficients[i] > coefficients[i + 1] for i in range(peak, degree))
    gaps = {i: coefficients[i-1] * coefficients[i+1] - coefficients[i] ** 2
            for i in range(1, degree)}
    breaks = [i for i, gap in gaps.items() if gap > 0]
    assert (count, degree, peak, breaks) == expected
    print(f"parameters={params} vertices={count} degree={degree} peak={peak}")
    print(f"breaks={breaks} positive defects={[gaps[i] for i in breaks]}")
    print(f"last five coefficients={coefficients[-5:]}")


if __name__ == "__main__":
    verify((0, 5, 3, 2), (70, 37, 21, [34, 36]))
    verify((3, 4, 2, 16), (312, 164, 95, [162, 163]))
    verify((7, 5, 2, 13), (315, 164, 97, [161, 162, 163]))
