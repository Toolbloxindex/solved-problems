# A counterexample to Songsuwan’s period-two conjecture for Node-Kayles

In Node-Kayles, a move deletes one vertex together with all its neighbors. The value of a position is the least nonnegative integer missing among the values of its options. Songsuwan’s Conjecture 2 predicts that the values eventually repeat at lag two when copies of a fixed level-regular rooted tree are attached by fresh edges to a single vertex of any fixed finite graph.

**Theorem.** There is a connected graph $G$ on 291 vertices with a vertex $u$ such that, if $B_k$ is formed by joining $u$ to one endpoint of each of $k$ disjoint five-vertex paths, then for every $j\geq0$,
$$
g(B_{4j+5})=8,\qquad g(B_{4j+7})=9.
$$
The endpoint-rooted path has branching vector $(1,1,1,1)$. Taking $j=N$ contradicts period two after any proposed onset $N$. The host contains cycles, so the tree-only question in Conjecture 1 remains open. [Source statement, §4](https://arxiv.org/html/2512.24221v2#S4)

## Literal host and its option sets

Write $P_n,C_n$ for the path and cycle on $n$ vertices, $\sqcup$ for disjoint union, and $\vee$ for complete join. Let $D_{n,m}$ have vertices $0,\ldots,n-1$ and the edge $ij$ with $j<i$ precisely when bit $i(i-1)/2+j$ of $m$ is set. In each expression mark vertex zero in the leftmost factor. Use

| Module | Graph | Quiet successor menu, as a bit mask |
|---|---|---:|
| 1 | $D_{5,20}$ | 7 |
| 2 | $((P_1\sqcup(D_{4,3}\sqcup P_3))\vee P_1)\sqcup C_{16}$ | 45 |
| 3 | $U\sqcup C_{18}$ | 71 |
| 4 | $((P_1\sqcup C_6)\vee D_{4,3})\sqcup C_{35}$ | 132 |
| 5 | $(D_{6,1174}\vee P_1)\sqcup(C_{35}\vee(C_{18}\vee C_{16}))$ | 227 |
| 6 | $U\sqcup (E\sqcup E)$ | 247 |
| 7 | $C_{78}\sqcup P_3$ | 1271 |

Here $U=D_{6,2353}\vee P_1$ and $E=D_{6,1110}\vee P_1$. Join these seven modules completely to one another. Add $u$ adjacent to all unmarked vertices and to none of the seven marked vertices. This gives a 280-vertex core. Attach two leaves and three separate three-vertex paths to $u$ by fresh edges to obtain $G$. Every module has an unmarked vertex, so the core is connected.

Let $W$ be the set of nimbers after a neighboring core move on the core with $u$ erased, and let $Q_i$ be the option set on the core after selecting mark $i$ and erasing $u$. Literal closed-neighborhood deletion gives $W=\{0,1,2,3\}$ and the seven masks above (bit $k$ represents value $k$). Each quiet move removes all the other marks. Its successor has a dominating hub, so it has zero surviving core after a hub move. A hub move on the original core leaves exactly the $K_7$ of marks, with value one. In module 7 a move at the mark leaves $P_{75}\sqcup P_3$. The path recurrence gives $Q(P_{75})=\{0,2,3,4,5,6,7,8\}$ and $g(P_{75})=1$. Since $Q(P_3)=\{0,1\}$ and $g(P_3)=2$, the quiet menu is $\{0,1,2,4,5,6,7,10\}$ as required. Other moves in this module give exactly $\{0,1,3\}$. The [independent checker](verify.py) computes all menus directly.

## Move equations and unbounded certificate

Use $x,c$ for the five- and three-edge ray counts and $z$ for the parity of a positive number of leaves. The leaf-pair identity permits one or two leaves as representatives. With a positive leaf, a two-edge ray toggles the nimber by one. In the following recurrences $F_0$ is the parent and $F_i$ its $i$th quiet successor. Set $d=3(x\bmod2)\oplus2(c\bmod2)\oplus z$, $e_i=\operatorname{mex}Q_i$, and $e_0=\operatorname{mex}(W\cup\{e_i:i>0\})$. The external moves on the parent give $W\oplus d$, $1\oplus(c\bmod2)$ and every $F_i(x,c,z)$. On child $i$ they give $Q_i\oplus d$ and $c\bmod2$. On either board also include $e_h\oplus d\oplus1$, attainable at a leaf and at any five-edge root, and $e_h\oplus d\oplus3$ when $c>0$. This uses path nimbers $g(P_j)=0,1,1,2,0,3$ for $j=0,\ldots,5$.

If $x>0$, the positions 2 and 3 of a five-edge ray give the two options $F_h(x-1,c,t)\oplus1$ for $t=0,1$. Position 4 creates one two-edge ray and duplicates the option at $t=z$. Position 5 gives $F_h(x-1,c+1,z)$. If $c>0$, positions 2 and 3 of a three-edge ray give $F_h(x,c-1,t)$ for $t=0,1$. All other moves were listed above. Thus the true graph value is the mex of this recurrence. It has a unique solution because an interior move decreases $2x+c$ and a quiet core move goes from parent to child. [Positive-leaf comparison](LeafIdentities.lean) · [Detailed literal move derivation](PeriodFourRealization.lean)

For any nonnegative $n$, let $C_b(n)$ fix $n<b$ and otherwise be $b+((n-b)\bmod4)$. Use $C_3$ on the minimum of $x,c$ and separately on the magnitude of their signed gap, keeping the sign. The candidate table is obtained by exact mex at these finite representatives and lookup through the same reduction. To verify its mex equation on an arbitrary input, use instead $C_4$ on the minimum and $C_5$ on the gap. If a large gap is shortened, its sign remains after either count changes by at most one, and its magnitude stays at least three. Smaller gaps are exact. Thus the change in the minimum is the same before and after the detailed reduction. Any shortened minimum remains at least three after the move. All residues modulo four and zero tests agree. Every normalized child, guard and constant XOR therefore agrees on the detailed representative. The detailed minimum ranges from zero through seven and the signed gap from minus eight through eight.

All $8\cdot 8\cdot 17\cdot 2=2176$ detailed mex equations passed. The recurrence uniqueness proves that the table gives the literal values for all $x,c,z$. At $c=3,z=0$, the entries at $x=5,7,9,11$ are $8,9,8,9$. For odd $x\ge7$, the gap $x-3\ge4$ is retained modulo four, so these entries prove the displayed unbounded equalities. The checks also give six for even $x\ge6$.

## Related work and authorship

Davis (November 26, 2026) and Schubr (Theorem 1.4, edition 1, November 27, 2026) prove period two under a condition on the residual branch. Deleting the far endpoint and its neighbor from an endpoint-rooted five-vertex path leaves a connected three-vertex path at the root. Schubr’s Theorem 1.5 gives a growing onset as the host varies. Here a single host violates period two arbitrarily late. Period-four double combs studied by Tavis Rudd vary the spine. A search through November 28, 2026 found no earlier public fixed-host disproof of Conjecture 2. Priority remains open. [Davis’s dated research note](https://github.com/1337isnot1337/solved-conjectures/blob/a02a340146c7f32f8e318a3059921b0648ff3831/research/songsuwan-node-kayles-branches/README.md) · [Schubr’s manuscript](https://research.luminaryoddities.org/all-research?edition=1&paper=node-kayles-depth-three-trees-repeated-rooted-branches) · [Rudd’s computations](https://github.com/tavisrudd/othello/blob/bf0d53148b0c6c4fb28cc3e612d86b6b09356c36/notes/2026-07-04-nk-trees-deep-dive.md)

Tomás Correia directed the research. Codex agents searched for the witness, developed the argument, formalized it and performed a separate computational review. The release is a research note with machine verification. This edition has had no external peer review.

## Reproducing the proof

Install Git, Python 3 and Elan. Run these commands in a fresh working directory.

```sh
git clone --depth 1 --branch v1.6.0 https://github.com/Toolbloxindex/solved-problems.git
git clone https://github.com/leanprover-community/mathlib4.git mathlib4
git -C mathlib4 checkout --detach 31ce06eaadf4a200c0e1407c5f10953cf606b8f8
cd mathlib4
lake exe cache get
proof_dir="$(cd ../solved-problems/results/songsuwan-node-kayles-counterexample && pwd)"
lake env python3 "$proof_dir/replay.py"
python3 "$proof_dir/verify.py"
```

Lean builds each release module in dependency order. The audit prints the two final theorem types and their axioms, which are confined to `propext`, `Classical.choice` and `Quot.sound`. The Python check independently reconstructs the residual graph options and compares the full finite certificate with the Lean table.

In [PeriodFourTarget.lean](PeriodFourTarget.lean), `hostEdge` specifies the fixed graph, `edge` specifies the fresh attachments, and `board k` selects the 291 original vertices and precisely the first $k$ paths. The score uses closed-neighborhood deletion in [GameValue.lean](GameValue.lean). In [PeriodFourProof.lean](PeriodFourProof.lean), `KaylesRays.PeriodFourGraph.counterexample_values` gives both values for every index, and `KaylesRays.PeriodFourGraph.songsuwan_conjecture_2_false` excludes every onset of period two.
