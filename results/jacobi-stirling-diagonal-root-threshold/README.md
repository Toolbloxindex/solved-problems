# The real-rootedness cutoff for Jacobi–Stirling diagonal numerators

## In brief

The Jacobi–Stirling numbers form a triangular array controlled by a real parameter. Each diagonal gives a generating series with a polynomial numerator. Lin and Zeng established when these numerators have only nonpositive zeros. Allowing positive zeros gives a wider range. At parameter 2 the second numerator is (x(9+34x-3x^2)), which has three real zeros. As the parameter increases past the cutoff, the second numerator develops a nonreal pair. Up to the cutoff, a change of variable and a weighted polynomial recurrence propagate real splitting to every higher diagonal.

## What this settles

For every real parameter (ugeq0), Lean proves that all positive-rank second-kind Jacobi–Stirling diagonal numerators split over the reals exactly when (uleq
ho), where (41/20<
ho<33/16), with the negative parameters and the two subsidiary assertions covered separately in writing.

## Why it matters

Substantial advance

The sharp cutoff extends Lin and Zeng’s nonpositive-root range and shows that the second diagonal decides whether all the numerators have real zeros for a fixed nonnegative parameter.

## Source and formalization

For (kgeq1), set (D_k(n;u)=operatorname{JS}(n+k,n;u)) using Lin and Zeng’s second-kind recurrence (1.2) and its boundary values. The theorem uses the numerator in their equation (2.1), namely ((1-x)^{3k+1}sum_{ngeq0}D_k(n;u)x^n). Its coefficient at (x) is ((1+u)^k), so it is nonzero throughout the formal range. The Lean index (m) denotes (k-1). The inverse change sends the split factor with projective root (-1) to the constant (1) and retains the rank-two degree drop at (u=2). [Lin–Zeng, equations (1.2) and (2.1)](https://arxiv.org/html/1309.4237v2#S2)

This release formalizes the main classification of the v1.14.0 written proof. The earlier tag also proves the all-real degree formula and gives a rank-two counterexample at (u=3) to an auxiliary positive-zero assertion in Lin and Zeng’s proof. Lin and Zeng’s Lemma 2.3 and Egge’s Legendre special case are earlier results. Ma and Wang’s fixed-coefficient theorem addresses coefficient extraction before taking the numerator. [Written proof at v1.14.0](https://github.com/Toolbloxindex/solved-problems/tree/v1.14.0/results/jacobi-stirling-diagonal-root-threshold) · [Separate negative range at v1.15.0](https://github.com/Toolbloxindex/solved-problems/tree/v1.15.0/results/jacobi-stirling-negative-interval) · [Egge’s Theorem 5.1](https://www.ericegge.net/papers/lsperm.pdf) · [Ma–Wang, §4](https://arxiv.org/html/2610.03111v1#S4)

The exact declaration is `JacobiProjective.sharp_nonnegative_source_series`. The pinned build uses Lean 4.37.0-rc1 at `0b77e12952ad39077d80d8bd6b66d601f225c321` and Mathlib at `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The theorem depends on `propext`, `Classical.choice` and `Quot.sound`. [Final module](JacobiSourceSeries.lean) · [Module order](LeanVerification.json)
