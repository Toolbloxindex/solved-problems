"""Check the counterexample directly from its edges, using only Python 3."""
from collections import deque
from itertools import combinations


def distances(graph, start):
    found = {start: 0}
    pending = deque([start])
    while pending:
        u = pending.popleft()
        for v in graph[u] - found.keys():
            found[v] = found[u] + 1
            pending.append(v)
    return found


def induced_extensions(graph, path):
    yield len(path)
    for v in graph[path[-1]] - set(path):
        if graph[v].isdisjoint(path[:-1]):
            yield from induced_extensions(graph, path + [v])


def main():
    graph = [set() for _ in range(19)]
    edges = [(i, i + 1) for i in range(14)] + [(0, 15), (0, 16), (14, 17), (14, 18)]
    for u, v in edges:
        graph[u].add(v)
        graph[v].add(u)
    assert len(distances(graph, 0)) == 19
    square = [{v for v, d in distances(graph, u).items() if 1 <= d <= 2} for u in range(19)]
    max_degree = max(map(len, square))
    hubs = [u for u in range(19) if len(square[u]) == max_degree]
    min_distance = min(distances(square, u)[v] for u, v in combinations(hubs, 2))
    longest = max(length for u in range(19) for length in induced_extensions(graph, [u]))

    for size in range(19, -1, -1):
        best = [s for s in combinations(range(19), size)
                if all(graph[u].isdisjoint(s) for u in s)]
        if best:
            break
    unique = len(best) == 1
    bound = (2 + int(unique)) * min_distance
    assert (size, len(best), max_degree, hubs, min_distance, longest, bound) == (
        11, 1, 5, [1, 13], 6, 17, 18)
    print(f"Unique maximum independent set: {best[0]}")
    print(f"Square maximum degree: {max_degree}, vertices: {hubs}, distance: {min_distance}")
    print(f"Longest induced path: {longest} vertices. Conjectured minimum: {bound}.")


if __name__ == "__main__":
    main()
