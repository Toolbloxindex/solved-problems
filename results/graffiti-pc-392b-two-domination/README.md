# Graffiti.pc 392b on 2-domination and matchings

For every finite simple connected graph $G=(V,E)$ on more than two vertices, let $A_\delta$ be the set of all vertices of minimum degree, and $A_2$ the set of vertices of degree exactly two. Write $X=\{v:|N(v)\cap A_2|=1\}$. Then

$$
\gamma_2(G)\leq \mu(G[V\setminus A_\delta])+|A_\delta|+|X|.
$$

Here $\gamma_2$ is the minimum size of a set $D$ such that every vertex outside $D$ has at least two neighbors in $D$. The matching number $\mu$ is the maximum number of pairwise vertex-disjoint edges. Graffiti.pc generated this conjecture, announced in January 2010 in Ermelinda DeLaViña's *Written on the Wall II*. The catalogue defines the invariants in entries 2, 46, 66, 90 and 100. [Statement 392b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) · [Definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json)

## Proof

Put $P=A_\delta\cup X$. We first color the vertices with two colors so that each vertex outside $P$ has at least two neighbors that belong to $P$ or have the opposite color. This local condition is enough because a vertex cover of the edges between different colors contains every such neighbor outside $P$ whenever the vertex itself is omitted.

Consider the set $I$ of vertices outside $P$ that have degree two and *both* neighbors of degree two. It admits a proper two-coloring. Indeed, each nonempty subset $S\subseteq I$ omits a minimum-degree vertex. Connectedness gives an edge from a vertex of $S$ to the outside of $S$. Its endpoint in $S$ has at most one neighbor in $S$. Delete that endpoint, color the rest inductively, and extend the coloring to the endpoint.

Keep this coloring on $I$. Color every other degree-two vertex white, and every vertex of degree different from two that has a degree-two neighbor black. Among extensions of these fixed colors, choose one maximizing the number of edges with different-colored endpoints. Flipping a free vertex shows that at least half its neighbors have the opposite color. We now check the local condition for a vertex $v\notin P$.

- If $v$ has degree two and has no degree-two neighbor, it is white and both its neighbors are black.
- If $v$ has degree two and has a degree-two neighbor, it has two such neighbors because $v\notin X$. Each neighbor outside $P$ sees $v$, hence likewise has two degree-two neighbors. These endpoints are all in $I$, where adjacent vertices have opposite colors.
- If $v$ has degree different from two and sees a degree-two vertex, it is black and has at least two degree-two neighbors. Any such neighbor outside $P$ has no degree-two neighbors. It sees $v$, so it cannot see two degree-two vertices, and membership outside $X$ excludes exactly one. It is therefore white.
- Otherwise $v$ is free. A connected graph of this order has no isolated vertex, and a vertex of degree one would have minimum degree. Thus $v$ has degree at least three. The maximum-cut condition gives at least two opposite-colored neighbors.

Let $B$ have vertex set $V\setminus P$ and just the edges with opposite-colored endpoints. It is bipartite. Choose a smallest vertex cover $C$ of $B$. By König's theorem there is a matching in $B$ of size $|C|$. For completeness, for any monochromatic subset $S$ of $C$, exchanging $S$ for its neighbors outside $C$ preserves the cover. Minimality therefore gives at least $|S|$ such neighbors. Hall's theorem matches the cover vertices of each color to distinct outside neighbors. The two matchings use disjoint vertices, since their sources are in $C$, their targets are outside $C$, and the two target colors differ.

For $v\notin C\cup P$, each of its two neighbors supplied by the local condition is in $P$ or joined to $v$ by an edge of $B$. In the second case the neighbor belongs to $C$. Thus $C\cup P$ is 2-dominating. Its size is at most $|C|+|A_\delta|+|X|$, and the matching in $B$ is also a matching in $G[V\setminus A_\delta]$. This proves the inequality even when $A_\delta$ and $X$ overlap.

## Comparison with the earlier bound

DeLaViña, Goddard, Henning, Pepper and Vaughan proved 392a in Theorem 3 of *Bounds on the k-domination number of a graph* (2011). At $k=2$, they delete **all** vertices of degree below three and add their number to the matching number of the remaining graph. Their proof already uses a maximum cut and a bipartite matching. When the minimum degree is two their bound implies 392b immediately. When the minimum degree is at least three they bound $\gamma_2$ by $\mu(G)$, and deleting $A_\delta$ loses at most $|A_\delta|$ matching edges. The additional content of 392b is the graphs with leaves. The constrained coloring explains how to keep degree-two vertices in the matching graph while paying for the particular set $X$. [2011 paper](https://doi.org/10.1016/j.aml.2011.01.013) · [Authors' proof, Theorem 3](https://www.uhd.edu/documents/academics/sciences/k-domination2010.pdf)

For a sharp comparison, subdivide each edge of $K_t$ once and attach one leaf to an original vertex, with $t\ge4$. There is one minimum-degree vertex and $X$ is empty. After removing the leaf, the $t$ original vertices cover all edges and can be matched to distinct subdivision vertices along a Hamilton cycle of $K_t$. Thus 392b gives $t+1$. The earlier bound gives $\binom t2+1$ because the original vertices induce an edgeless graph. To attain the new bound take the leaf and all original vertices. Conversely the leaf is compulsory. If $j$ original vertices are omitted, every subdivision vertex on an edge incident with one of them must be selected. The $j$ omitted vertices already give $j$ distinct such edges by taking their successors on the Hamilton cycle. At least $t$ vertices besides the leaf are therefore required. This family is a written comparison. The Lean declaration below proves the general inequality.

Ryan Pepper's Corollary 2 in *Implications of Some Observations About the k-Domination Number* (2010) gives another close bound. With leaves $L$ it gives $|L|+\tau(G-L)$, where $\tau$ is the minimum vertex-cover size. This already implies 392b whenever the nonleaf graph has equal cover and matching numbers, in particular for bipartite graphs. It also covers the subdivided-clique example above. [Pepper, Corollary 2](https://www.researchgate.net/publication/247768193_Implications_of_Some_Observations_About_the_k-Domination_Number)

To separate 392b from *both* of these earlier bounds, attach a disjoint $K_5$ to an original vertex by one bridge in the same example. The leaf and $X$ are unchanged. After deleting the leaf, a matching has at most $t$ edges incident to original vertices and at most two further edges in the clique. These $t+2$ edges are attained. The minimum cover has size $t+4$, from disjoint lower bounds of $t$ on the incidence graph and four on the clique. Selecting the original vertices and four clique vertices attains it. The vertices of degree at least three induce a $K_5$ with the bridge and otherwise isolated vertices. This graph has matching number three. Consequently the bounds from 392b, Pepper's Corollary 2, and 392a are respectively $t+3$, $t+5$, and $\binom{t}{2}+4$. The first is exact. The earlier lower-bound argument still forces the leaf and at least $t$ original or subdivision vertices. At least two clique vertices must also be selected, since only one clique vertex has an outside neighbor. The leaf, the original vertices and two clique vertices suffice.

## Statement-to-theorem mapping

| Source quantity or hypothesis | Lean interpretation |
| --- | --- |
| Every finite simple undirected graph on $n>2$ vertices | An arbitrary `G : Graffiti392.Graph n` on `Fin n`, with symmetric loopless adjacency and hypothesis `2 < n`. Every finite vertex set admits such a labeling. |
| Connected | `G.Connected` requires an edge across every nonempty proper vertex cut. |
| $N(v)$, degree | `G.nbr v` filters all vertices by adjacency. `G.degree v` is its cardinality. |
| $A_\delta$, $A_2$, $X$ | `G.minimum` compares the degree to every vertex's degree. `G.two` tests equality to two. `G.exceptional` counts membership in the intersection of each open neighborhood with `G.two` and tests equality to one. |
| $\gamma_2(G)$ | `G.gammaTwo` minimizes the cardinality of a 2-dominating set. `gammaTwo_attained` and `gammaTwo_le` establish attainment and minimality. |
| $\mu(G[U])$ | `G.Matches U s` selects edges from a set of representatives in $U$ to distinct partners in $U$ outside that set. These edges are vertex-disjoint. Conversely, orient each edge of any matching arbitrarily and take its tails as representatives. `matching_attained` and `le_matching` prove the extremal characterization. |
| Conjecture 392b | `Graffiti392.Graph.conjecture392b` bounds `G.gammaTwo` by the matching number on the complement of `G.minimum` plus the two separate cardinalities. |

The only final declaration in the manifest is the full source inequality. The compiler checks the coloring and cover construction and uses Mathlib's finite Hall theorem. The five project modules are listed in dependency order. [Final theorem](Conjecture392b.lean) · [Verification manifest](LeanVerification.json)

A 26 November 2026 rebuild compiled all five project sources in a fresh directory with Lean 4.37.0-rc1, compiler commit `0b77e12952ad39077d80d8bd6b66d601f225c321`, and the Mathlib revision below. Inspecting the resulting declaration confirmed both source hypotheses and the displayed bound. Its complete axiom report was `[propext, Classical.choice, Quot.sound]`. The pinned Lean kernel also replayed all five resulting modules. Nanoda independently typechecked the full transitive export of the final theorem, 6,123 declarations, with zero errors and a hard three-axiom allowlist. The export SHA-256 was `9b4c187b97af6bc0e53289b3d2a25a0963a0a4d6f3c6befad234a2cbc0abd1f3`. One investigator performed the checks. External mathematical review and priority assessment remain open.

## Reproduction

Create the following Lean toolchain and Lake configuration with Mathlib pinned at `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. From this directory in a fresh checkout run the following commands.

```sh
cat > lean-toolchain <<'EOF'
leanprover/lean4:v4.37.0-rc1
EOF
cat > lakefile.toml <<'EOF'
name = "graffiti392b"
version = "1.0.0"
defaultTargets = ["Conjecture392b"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "31ce06eaadf4a200c0e1407c5f10953cf606b8f8"

[[lean_lib]]
name = "Graph392"

[[lean_lib]]
name = "Cut392"

[[lean_lib]]
name = "Color392"

[[lean_lib]]
name = "Cover392"

[[lean_lib]]
name = "Conjecture392b"
EOF
lake update
lake build Conjecture392b
printf '%s\n' 'import Conjecture392b' '#check Graffiti392.Graph.conjecture392b' \
  '#print axioms Graffiti392.Graph.conjecture392b' | lake env lean --stdin
```

## Earlier work and finite controls

The 26 November 2026 search covered the original entry and definitions, the 2010 preprint and its 2011 publication, other Graffiti.pc papers on 2-domination, and subsequent searches by formula, minimum-degree deletion, degree-two neighborhoods, bipartite covers and matching bounds. The Davis catalogue, issue discussions and recent commits through 9e0cb5a46 were checked. The related entry 392c already has a counterexample from Derek Blair. Kiankyars records tests of 392b through order ten and larger heuristic searches. The proof here resolves the formula in 392b at every order. Priority remains undetermined. [Related paper by DeLaViña, Larson, Pepper and Waller](https://math1um.github.io/Research/r07.pdf) · [Davis catalogue](https://itsdavis.com/solved-conjectures/catalogue/) · [Earlier computational work](https://github.com/kiankyars/math/blob/master/wowii/NOTES.md) · [Blair's 392c result](https://github.com/derekblair/math-proofs/commit/3e404e229a3ffe04057f84d7379e3bb9d34b19f8)

Independent exact enumeration of dominating sets and a matching recursion on all 11,117 connected graphs of order eight gave 759 equalities in 392b. Its bound was strictly smaller than the 392a bound on 255 graphs. On the subdivided-clique examples the computed triples $(\gamma_2,\text{392b bound},\text{392a bound})$ were $(5,5,7)$, $(6,6,11)$ and $(7,7,16)$ for $t=4,5,6$, agreeing with the formulas above. These computations are separate from the Lean proof. [McKay's graph6 census](https://users.cecs.anu.edu.au/~bdm/data/graphs.html)

Bujtás and Jaskó's 25 December 2016 paper with a similar title gives order-based bounds at fixed minimum degree, including improvements at degrees 6 through 21. Its stated bounds concern a different parameter range from the residual leaf case here. [Bujtás and Jaskó](https://arxiv.org/abs/1612.08301)

The direct checks use Python's standard library. Run `python3 check_examples.py` for the three subdivided-clique comparisons and both five-clique extensions. For the extensions at $t=4,5$ the computed quadruples (actual, 392b, 392a, Pepper) were $(7,7,10,9)$ and $(8,8,14,10)$, exactly as predicted. For the full finite control, pass `--census graph8c.g6` with the connected order-eight graph6 file from McKay's collection. Its SHA-256 is `0002354f1ab3344a2706626a037ad15367bf23a2163aa68f552c3a169ca9a036`. [Verification source](check_examples.py)

The comparison with Pepper’s full Theorem 1 gives the same bound on the pendant example. On the bridged five-clique family its whole-graph bound is two larger, although splitting that example at the bridge recovers the sharper value. No earlier proof of the full statement surfaced in our review. This AI-assisted formal proof is published by Tomás Correia.
