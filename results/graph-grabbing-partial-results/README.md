# Two partial results on the Seacrest–Seacrest graph-grabbing conjecture

Alice and Bob alternately remove a vertex from a finite connected graph, keeping the remaining graph connected until it is empty. Each collects the weight of each vertex they remove. Alice moves first. Seacrest and Seacrest ask whether she can always collect at least half the total nonnegative weight when the graph is bipartite and has an even number of vertices. The unrestricted conjecture remains open.

## A strategy for separated positive weights

Let the graph be connected, bipartite and of even order. Assume it has no induced copy of the seven-vertex tree formed by subdividing each edge of a three-leaf star once. If adjacent vertices of positive weight have equal weights, Alice can guarantee at least half the total weight.

Equivalently, the weight may be a different positive real constant on each connected component of the positive-weight vertices. In particular, when all positive-weight vertices form an independent set, their weights may differ arbitrarily. Either bipartition class may contain positive vertices.

The strategy uses a capture lemma. On the same class of graphs, mark vertices in one bipartition class. If at most one marked vertex can be removed initially, Alice can take every marked vertex.

A legal deletion can expose at most one previously unavailable vertex, and that vertex must be the deleted vertex’s only remaining neighbor. Suppose every opening exposed a vertex of a specified color. All removable vertices would be leaves of the other color. Under the induced-tree exclusion, the structural lemma in the proof then bounds every degree by two. Connectivity forces a path with both endpoints of the other color, which has odd order. Thus an even position always offers an opening which exposes no vertex of the specified color.

Alice takes the unique available marked vertex when there is one. Its neighbors have the opposite color. With no available marked vertex, she takes an opening that keeps all marks unavailable. Bob can expose at most one mark on his turn, so the argument repeats on the remaining induced graph.

For the weighted theorem, Alice takes a heaviest available positive vertex whenever she can. A previously available reply has at most its weight. A newly available positive reply is adjacent to Alice’s move and has equal weight by hypothesis. The remaining even position inherits the hypotheses. If every available vertex has weight zero, Alice marks the positive vertices of the heavier bipartition class and applies the capture lemma.

## Choosing an endpoint to retain on a path with leaves

Take a path on an even number of vertices and attach at most one additional leaf at each path vertex. Assume the number of attached leaves is even and one endpoint of the path carries a lightest such leaf. The path vertices may have arbitrary real weights and the attached leaves have nonnegative weights.

Play twice with identical weights. In the first game one specified path endpoint must survive until the final move. In the second game the opposite endpoint must survive. Under optimal play, the sum of Alice’s two margins is nonnegative. Here a margin is Alice’s weight minus Bob’s. In particular, at least one choice of endpoint allows Alice to tie or win.

Number the path vertices from the retained endpoint, starting at zero. The path vertices disappear in reverse order. When an even number remain and the last of them is uncovered, Alice takes it. Otherwise she takes a heaviest eligible leaf. With an even number of path vertices remaining, she leaves the leaf on the last path vertex in place. Counting the remaining vertices proves an eligible move exists whenever her turn begins.

This strategy gives Alice the odd-indexed path vertices. Reversing the path exchanges odd and even indices, so across both plays she receives one copy of the total path weight. Now fix a leaf-weight threshold and count the leaves at or above it. In either game Alice can take at least half that count rounded down. She gets the rounded-up bound if the far endpoint bears a leaf below the threshold. For thresholds above the weight of the designated lightest leaf, one of the two orientations has this extra guarantee. At all lower thresholds the count is the full even number of leaves. Adding the guarantees and summing over the successive differences between distinct leaf weights gives her at least one copy of the total leaf weight across the two games. The implementation verifies every legal opponent reply and identifies the path recurrence with connectivity-preserving play.

For example, give four successive path vertices weights 0, 0, 0, 2 and attach a leaf of weight 1 at the first and a leaf of weight 2 at the last. The whole graph is a six-vertex path. The choice of retained vertex changes who wins.

| Retained path vertex | Margin after opening at the weight-1 leaf | Margin after opening at the weight-2 leaf | Optimal margin |
| --- | ---: | ---: | ---: |
| First | +1 | +1 | +1 |
| Last | −3 | −1 | −1 |

To check the table, write the weights along the full path as 1, 0, 0, 0, 2, 2. For each surviving interval, take the maximum of the removed end’s weight minus the value of the shorter interval. Skip a move that removes the retained vertex before the interval has length one. A singleton has value equal to its weight. The two optimal margins sum to zero, so equality is possible in the theorem.

## Scope and earlier work

Seacrest and Seacrest proved the unrestricted-weight result on even trees. The second result above compares two games that impose a last-move requirement, so it addresses a different question even on a tree. Eoh and Choi studied binary weights on graphs with forbidden induced configurations. Doki, Egawa and Matsumoto obtained results for other forbidden-subgraph classes. Boriboon and Kittipassorn proved results on blow-ups of trees and cycles and developed comparisons for rooted games. Hollom disproved a stronger conjecture that permits nonbipartite graphs. This note makes no claim of discovery priority and has not undergone external peer review. [Seacrest and Seacrest](https://doi.org/10.1016/j.disc.2012.01.010) · [Eoh and Choi](https://arxiv.org/abs/1810.03121) · [Doki, Egawa and Matsumoto](https://doi.org/10.7151/dmgt.2440) · [Boriboon and Kittipassorn](https://arxiv.org/abs/2007.11805) · [Hollom](https://arxiv.org/abs/2311.02109)

## Formal statements and reproduction

The Toolbloxindex research project developed these arguments and their formalization with OpenAI Codex assistance.

| Lean declaration | Mathematical statement |
| --- | --- |
| `GraphGrabbing.capture_color` | Alice captures a marked set in one color class with at most one initially removable mark. The equivalent induced-tree exclusion is in `longClaw_iff_induced`. |
| `GraphGrabbing.win_equal_positive_edges` | Alice guarantees a nonnegative margin under the graph and weight hypotheses above. |
| `GraphGrabbing.Comb.opposite_rooted_values` | The two optimal rooted margins sum to a nonnegative number for the stated path and leaf placements. |

The release contains all five project modules. Starting from this directory with Git, Bash and elan installed, run the following on a machine with access to the Mathlib cache.

```bash
set -eu
bundle="$PWD"
work=$(mktemp -d)
git clone --quiet https://github.com/leanprover-community/mathlib4.git "$work/mathlib"
cd "$work/mathlib"
git checkout --quiet 31ce06eaadf4a200c0e1407c5f10953cf606b8f8
lake exe cache get
export LEAN_PATH="$work:$(lake env printenv LEAN_PATH)"
for module in GrabbingGraph GrabbingClaw GrabbingCapture GrabbingComb GrabbingCombGraph
do
  cp "$bundle/$module.lean" "$work/$module.lean"
  (cd "$work" && elan run leanprover/lean4:v4.37.0-rc1 lean -DwarningAsError=true -o "$module.olean" "$module.lean")
done
```

The compilation prints axiom audits for the three final declarations. Each uses only propositional extensionality, classical choice and quotient soundness. The module order and declaration names are also in `LeanVerification.json`.
