# Solved Problems

Proofs and counterexamples in graph theory, combinatorial games and enumerative combinatorics. Each release below links to its mathematical statement and explains what was checked. The three type B q-Stirling releases build on one another. [Browse the proof archive](https://www.tomdco.com/proofs) · [Machine-readable release index](publications.json)

## A game where two more paths change the answer

In Node-Kayles, a move removes a vertex and all its neighbors. Songsuwan asked whether attaching enough copies of the same rooted tree to a fixed graph eventually makes the game value repeat every two copies. Our counterexample uses a fixed graph on 291 vertices and copies of a five-vertex path. With $4j+5$ copies the value is 8. With $4j+7$ copies it is 9, for every integer $j \geq 0$. The host graph contains cycles. The separate question about level-regular trees remains open. [Proof and construction](results/songsuwan-node-kayles-counterexample/README.md) · [Archived release](https://doi.org/10.5281/zenodo.24614057)

There are two ways to inspect the result. Lean proves the formulas for every $j$. An independent Python program recomputes all 2,176 entries of the finite certificate. To run that check from the repository root, use the command below. The result directory also gives the pinned Lean toolchain and replay instructions. [Lean theorem](results/songsuwan-node-kayles-counterexample/PeriodFourProof.lean) · [Palomar preflight](https://github.com/Toolbloxindex/solved-problems/actions/runs/46088028046)

```sh
python3 results/songsuwan-node-kayles-counterexample/verify.py
```

## Results by release

| Release | Problem and result | Verification |
| --- | --- | --- |
| v1.6.0 | [Songsuwan, Node-Kayles](results/songsuwan-node-kayles-counterexample/README.md) · A fixed graph disproves eventual period two in Conjecture 2. | Lean proof for all branch counts in two progressions. Independent Python certificate check. |
| v1.5.0 | [Seacrest–Seacrest, graph grabbing](results/graph-grabbing-partial-results/README.md) · Alice secures half the weight on a restricted class of weighted bipartite graphs. A second result compares two choices of final vertex on a path with attached leaves. | Three Lean theorems with an axiom audit. The general conjecture remains open. |
| v1.4.0 | [Type B q-Stirling coefficients](results/type-b-q-stirling-coefficients/README.md) · A combined account of the first-column and second-diagonal inequalities in the two families. | Seven final Lean declarations across eight modules. |
| v1.3.0 | [Sagan–Swanson, parity log-concavity](results/sagan-swanson-column-one/README.md) · The parity inequality holds on the rising side of first-kind column one and on the second diagonal in both families. | Lean proofs from the coefficient recurrences. |
| v1.2.0 | [Graffiti.pc 392b, 2-domination and matchings](results/graffiti-pc-392b-two-domination/README.md) · The proposed matching bound holds for every finite simple connected graph on at least three vertices. | Lean proof of the full bound. [Zenodo archive](https://doi.org/10.5281/zenodo.24571980) |
| v1.1.0 | [Graffiti.pc 138, induced paths](results/wowii-138/README.md) · The conjecture requires an induced path on at least 18 vertices in a particular tree. Its longest path has 17. | Exhaustive Python check of the 19-vertex tree and a written proof for an infinite family. |
| v1.0.0 | [Type B q-Stirling numbers, second-kind column one](results/first-column/README.md) · Among ranks $n \geq 2$, all interior coefficient gaps are strictly positive exactly when $n \geq 6$. | Lean classification for all ranks and a Python replay through row 256. |

To cite a result, use its title and DOI where available, or give the release tag and the exact theorem you used. Corrections, earlier references and independent replays are welcome. [Open an issue](https://github.com/Toolbloxindex/solved-problems/issues)
