# Log-concavity in the first columns and second diagonal of the type B q-Stirling arrays

Strict adjacent log-concavity in second-kind column one has threshold rank six for ranks at least two. The first-kind rising-side midpoint inequality holds in column one, and both families satisfy the parity inequality on the second diagonal. At rank five the only interior equality in second-kind column one is at degree one. The all-column conjecture remains open.

Tomás Correia directed the AI-assisted development with Codex. The two tagged releases contain the proofs, examples, and original statements.

- https://github.com/Toolbloxindex/solved-problems/tree/v1.0.0/results/first-column
- https://github.com/Toolbloxindex/solved-problems/tree/v1.3.0/results/sagan-swanson-column-one

Build with `lake build`. Challenge.lean states the seven results with their defining recurrences. Solution.lean identifies those recurrences with the published coefficients and applies the proofs from the two releases. Run `lake comparator` with the pinned toolchain and comparator.json.
