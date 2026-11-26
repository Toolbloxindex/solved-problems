# Strict log-concavity in the first type-B q-Stirling column

November 26, 2026 · Version 1.0.0 · AI-assisted research note

For the type-B q-Stirling polynomial of the second kind with column index k = 1, when is each interior coefficient strictly greater than the geometric mean of its two neighbors?

**Theorem.** For n ≥ 2, all interior coefficients satisfy a(d)² > a(d−1)a(d+1) exactly when n ≥ 6. At n = 5 there is exactly one equality, at degree 1. At n = 2, 3, 4 the inequality fails at degree 1. The row n = 1 is constant and has no interior degrees.

Sagan and Swanson ask for weak log-concavity within each parity class for both type-B families and all columns. This result classifies the stronger adjacent-coefficient property in one column of one family. The wider conjecture remains outside this proof. Priority in the literature is unestablished. [Sagan and Swanson, Definition 1.5 and Conjecture 7.5](https://users.math.msu.edu/users/bsagan/Papers/Old/qStB-pub.pdf)

## Proof

Write Fₙ for the first-column polynomial. Its recurrence gives F₁ = 1 and Fₙ₊₁ = 1 + (1+q+q²)Fₙ. Thus Fₙ is the sum of (1+q+q²)ʲ for 0 ≤ j < n. All coefficients from degree 0 through 2n−2 are positive. Extend the sequence by zero beyond this interval.

The coefficients at degrees 0, 1 and 2 are n, n(n−1)/2 and (n+1)n(n−1)/6. These follow by choosing one linear factor, one quadratic factor or two linear factors in each power, then summing over j. At degree 1 the gap is therefore

    a(1)² − a(0)a(2) = n²(n−1)(n−5)/12.

This gives the failures at n = 2, 3, 4 and the equality at n = 5. At n = 5 the full row is (5, 10, 20, 25, 26, 19, 11, 4, 1). Its successive interior gaps are 0, 150, 105, 201, 75, 45, 5.

For the induction, let a be the row at n ≥ 5 and b the coefficients after multiplication by 1+q+q². Suppose a is weakly log-concave and every interior gap at degree ≥ 2 is positive. On the positive support, consecutive ratios a(i)/a(i−1) are nonincreasing. Hence a(i)a(j) ≥ a(i−1)a(j+1) for i ≤ j. The same inequality holds on the zero extension, since a positive right-hand side places both intermediate indices inside the support.

Fix a new interior degree d ≥ 2. Set xⱼ = a(d−3+j) for j = 0,…,4. Expanding b(d)² − b(d−1)b(d+1) gives

    (x₁² − x₀x₂) + (x₁x₂ − x₀x₃) + (x₁x₃ − x₀x₄)
      + (x₂x₃ − x₁x₄) + (x₃² − x₂x₄).

Every term is nonnegative by the ratio inequality. Write D = 2n−2. When 2 ≤ d < D, the last term is the positive gap of a at d. At d = D the last term equals a(D)² > 0. At d = D+1 the first term is the positive gap at D−1. This covers the entire new interior from degree 2 onward. The extra constant 1 in Fₙ₊₁ affects only degree 0 and hence leaves these gaps intact. The explicit degree-one formula is strictly positive in every new row n+1 ≥ 6. Induction proves the classification.

## Reproduce

From the repository root, run the following commands. The pinned Lean version uses its standard library. The Python replay uses only the standard library.

```sh
lean results/first-column/FirstColumn.lean
python3 results/first-column/check.py
```

The Lean file identifies the polynomial with the original second-kind recurrence. Its theorems `original_column_strict_iff` and `original_column_five_equality_iff` establish the two strictness claims. The printed axiom lists contain propext, Classical.choice and Quot.sound. The Python check calculates rows through n = 256 and independently reconstructs the first eighteen rows by multinomial expansion. Only the induction and Lean proof cover all n.

The project used AI to develop the proof and formalization. The verification records a Lean kernel check and a separate integer computation. External peer review and a priority determination are open.
