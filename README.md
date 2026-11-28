# Log-concavity in the first columns and second diagonal of the type B q-Stirling arrays

Strict adjacent log-concavity in second-kind column one has threshold rank six for ranks at least two. The first-kind rising-side midpoint inequality holds in column one, and both families satisfy the parity inequality on the second diagonal. At rank five the only interior equality in second-kind column one is at degree one. The all-column conjecture remains open.

In first-kind column one of rank r+1, write T(r)=r(r−1)/2. At every integer degree d with d ≤ T(r) or d+1 < T(r+1), the square of the coefficient at d is at least the product at d−2 and d+2. This controls the lower part of each parity subsequence. Across all degrees the coefficients increase weakly up to a peak p and decrease weakly thereafter, with T(r) ≤ p ≤ T(r+1). A plateau is possible.

For every column k from 0 through the rank n, the coefficients of each family are positive at every integer degree from 0 through its degree bound, inclusive, and vanish everywhere else. The bound is n(n−1)−k(k−1) for the first kind and 2k(n−k) for the second.

Tomás Correia directed the AI-assisted development with Codex. The two tagged releases contain the proofs, examples, and original statements.

- https://github.com/Toolbloxindex/solved-problems/tree/v1.0.0/results/first-column
- https://github.com/Toolbloxindex/solved-problems/tree/v1.3.0/results/sagan-swanson-column-one

Build with `lake build`. Challenge.lean states the seven results with their defining recurrences. Solution.lean identifies those recurrences with the published coefficients and applies the proofs from the two releases. Run `lake comparator` with the pinned toolchain and comparator-stirling.json.
