# Coefficient inequalities for the type B q-Stirling numbers

Tomás Correia · November 2026 · Technical note with Lean proofs

A combined technical note on seven Lean-verified results. Strict adjacent log-concavity in second-kind column one begins at rank six for ranks at least two. The note also proves a rising-side inequality in first-kind column one and parity log-concavity on the second diagonal of both families. The full all-column question remains open.

## Second-kind column one

For rank $n\ge 2$, every interior coefficient strictly exceeds the geometric mean of its neighbors exactly when $n\ge 6$. At rank five, equality holds only at degree one.

Write Fₙ for the first-column polynomial. Its recurrence gives F₁ = 1 and Fₙ₊₁ = 1 + (1+q+q²)Fₙ. Thus Fₙ is the sum of (1+q+q²)ʲ for 0 ≤ j < n. All coefficients from degree 0 through 2n−2 are positive. Extend the sequence by zero beyond this interval.

The coefficients at degrees 0, 1 and 2 are n, n(n−1)/2 and (n+1)n(n−1)/6. These follow by choosing one linear factor, one quadratic factor or two linear factors in each power, then summing over j. At degree 1 the gap is therefore

    a(1)² − a(0)a(2) = n²(n−1)(n−5)/12.

This gives the failures at n = 2, 3, 4 and the equality at n = 5. At n = 5 the full row is (5, 10, 20, 25, 26, 19, 11, 4, 1). Its successive interior gaps are 0, 150, 105, 201, 75, 45, 5.

For the induction, let a be the row at n ≥ 5 and b the coefficients after multiplication by 1+q+q². Suppose a is weakly log-concave and every interior gap at degree ≥ 2 is positive. On the positive support, consecutive ratios a(i)/a(i−1) are nonincreasing. Hence a(i)a(j) ≥ a(i−1)a(j+1) for i ≤ j. The same inequality holds on the zero extension, since a positive right-hand side places both intermediate indices inside the support.

Fix a new interior degree d ≥ 2. Set xⱼ = a(d−3+j) for j = 0,…,4. Expanding b(d)² − b(d−1)b(d+1) gives

    (x₁² − x₀x₂) + (x₁x₂ − x₀x₃) + (x₁x₃ − x₀x₄)
      + (x₂x₃ − x₁x₄) + (x₃² − x₂x₄).

Every term is nonnegative by the ratio inequality. Write D = 2n−2. When 2 ≤ d < D, the last term is the positive gap of a at d. At d = D the last term equals a(D)² > 0. At d = D+1 the first term is the positive gap at D−1. This covers the entire new interior from degree 2 onward. The extra constant 1 in Fₙ₊₁ affects only degree 0 and hence leaves these gaps intact. The explicit degree-one formula is strictly positive in every new row n+1 ≥ 6. Induction proves the classification.

## First-kind column one and the second diagonal

Let $a_d$ be the coefficient of $q^d$ in the unsigned first-kind polynomial $c_B[r+1,1]$, extended by zero outside its support. For every $r\ge0$, integer $d$, and integer stride $s\ge0$, we prove

$$a_{d-s}\le a_{d+s}\quad\Longrightarrow\quad a_{d-s}a_{d+s}\le a_d^2.$$

Setting $s=2$ gives the parity inequality of Sagan and Swanson in this range. The same column is unimodal, with a peak between $T_r$ and $T_{r+1}$ inclusive, where $T_r=r(r-1)/2$. The stride-two inequality holds whenever $d\le T_r$ or $d+1<T_{r+1}$, without comparing the coefficients first.

The accompanying recurrence proofs also give positive coefficients throughout the support for both type B families and the stride-two inequality in both families on the entire second diagonal $k=n-2$, for $n\ge2$. These results leave the unrestricted parity conjecture open.

### Proof of the rising-side inequality

Write $W_i=1+q+\cdots+q^{2i}$. The first-kind column is the sum of the products obtained by omitting one factor from $W_0\cdots W_r$. Each product is symmetric about its own center. The centers range from $T_r$ to $T_{r+1}$. Sliding a window changes the sum by the entering coefficient minus the leaving coefficient. Applied to the omitted products, this gives increasing and decreasing outer portions and arithmetic concavity through the central band.

For the stride inequality, compare two omitted products at a time. After factoring out their common windows, each remaining factor is a single window. For nonnegative weights the tilted difference $A f(x+s)-B f(x)$ of the two-window mixture cannot change from negative back to positive when $0\le A\le B$. Sliding-window summation preserves this sign property. At the target degree choose $A=a_{d-s}+a_d$ and $B=a_d+a_{d+s}$. The hypothesis gives the required ordering. The weighted two-term comparisons then combine by balancing positive and negative summands at this tilt. Expanding the resulting inequality yields the theorem. On the falling side this choice can reverse the ordering, which is why the argument gives a one-sided conclusion.

## Formal statements

The original coefficient recurrences (12) and (14) are represented by `FirstColumn.sb` and `StirlingRecurrence.cb`. In `StirlingRecurrence.coeff`, true selects the first kind and false selects the second. The integer degree convention includes both zero-padded ends.

| Declaration | Mathematical scope |
| --- | --- |
| `FirstColumn.original_column_strict_iff` | Strict adjacent log-concavity classification |
| `FirstColumn.original_column_five_equality_iff` | Unique interior equality at rank five |
| `StirlingBoxes.OmissionCenter.column_one_rising_gap` | The implication above for every stride |
| `StirlingBoxes.OmissionCenter.column_one_lower_parity` | Degree-only sufficient condition at stride two |
| `StirlingBoxes.OmissionCenter.column_one_unimodal` | Unimodality and the peak interval |
| `StirlingRecurrence.recurrence_support` | Exact positive support, both families |
| `StirlingRecurrence.recurrence_second_parity` | Every degree on the second diagonal, both families |

## Reproduction

Prerequisites are Git, Bash, elan, and the Lean and Mathlib caches for the stated revisions. Run these commands from the directory containing this README. The checkout of Mathlib supplies its pinned Lean toolchain and dependencies.

```bash
set -eu
bundle="$PWD"
work=$(mktemp -d)
git clone --quiet https://github.com/leanprover-community/mathlib4.git "$work/mathlib"
cd "$work/mathlib"
git checkout --quiet 31ce06eaadf4a200c0e1407c5f10953cf606b8f8
lake exe cache get
export LEAN_PATH="$work:$(lake env printenv LEAN_PATH)"
for module in FirstColumn SecondDiagonal PairBridge StirlingDiagonal RecurrenceBridge MarkedAlphabet OmissionCenter OmissionRising
do
  cp "$bundle/$module.lean" "$work/$module.lean"
  (cd "$work" && elan run leanprover/lean4:v4.37.0-rc1 lean -DwarningAsError=true -o "$module.olean" "$module.lean")
done
```

Expected output includes the final theorem names and axiom lists containing only standard Lean axioms (propositional extensionality, classical choice and quotient soundness). The machine-readable manifest lists the modules and final declarations.

## Attribution and status

Bruce E. Sagan and Joshua P. Swanson formulated Conjecture 7.5 in *q-Stirling numbers in type B*, European Journal of Combinatorics 118 (2024), 103899. Their Definition 1.5 supplies the recurrences, and Theorem 2.1 gives the symmetric-function formulas underlying the omission proof. The present partial results and formalizations were developed by the Toolbloxindex research project with OpenAI Codex assistance. They have not undergone external peer review. We make no priority claim. [Original paper](https://doi.org/10.1016/j.ejc.2023.103899)

## Relationship to prior work

Sagan and Swanson, q-Stirling numbers in type B (doi:10.1016/j.ejc.2023.103899), give the recurrences in Definition 1.5, symmetric-function formulas in Theorem 2.1, and the parity question in Conjecture 7.5. Their Theorem 7.2 and Corollary 7.3 compare polynomials across columns. The inequalities here compare coefficients within a fixed polynomial. Bottom-heaviness (Conjecture 7.6) compares reflected degrees, and asymptotic normality (Conjecture 7.8) describes a limiting distribution. This note consolidates the project’s proofs from GitHub releases v1.0.0 and v1.3.0 and makes no claim of discovery priority. The two earlier releases contain the original arguments. The independently run Comparator preflight checked a module-format port of all seven statements.

- [Second-kind proof and finite replay](https://github.com/Toolbloxindex/solved-problems/tree/v1.0.0/results/first-column)
- [Rising-side, support and diagonal proofs](https://github.com/Toolbloxindex/solved-problems/tree/v1.3.0/results/sagan-swanson-column-one)
- [Comparator report run](https://github.com/Toolbloxindex/solved-problems/actions/runs/46004800699)
- [Bottom-heaviness proof](https://www.trureturing.org/research/ss2205-bottomheavy/)
- [Asymptotic normality result](https://itsdavis.com/solved-conjectures/results/sagan-swanson-normality/)
