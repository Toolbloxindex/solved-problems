# One-sided log-concavity for a column of the type B q-Stirling numbers

Let $a_d$ be the coefficient of $q^d$ in the unsigned first-kind polynomial $c_B[r+1,1]$, extended by zero outside its support. For every $r\ge0$, integer $d$, and integer stride $s\ge0$, we prove

$$a_{d-s}\le a_{d+s}\quad\Longrightarrow\quad a_{d-s}a_{d+s}\le a_d^2.$$

Setting $s=2$ gives the parity inequality of Sagan and Swanson in this range. The same column is unimodal, with a peak between $T_r$ and $T_{r+1}$ inclusive, where $T_r=r(r-1)/2$. The stride-two inequality holds whenever $d\le T_r$ or $d+1<T_{r+1}$, without comparing the coefficients first.

The accompanying recurrence proofs also give positive coefficients throughout the support for both type B families and the stride-two inequality in both families on the entire second diagonal $k=n-2$, for $n\ge2$. These results leave the unrestricted parity conjecture open.

## Proof

Write $W_i=1+q+\cdots+q^{2i}$. The first-kind column is the sum of the products obtained by omitting one factor from $W_0\cdots W_r$. Each product is symmetric about its own center. The centers range from $T_r$ to $T_{r+1}$. Sliding a window changes the sum by the entering coefficient minus the leaving coefficient. Applied to the omitted products, this gives increasing and decreasing outer portions and arithmetic concavity through the central band.

For the stride inequality, compare two omitted products at a time. After factoring out their common windows, each remaining factor is a single window. For nonnegative weights the tilted difference $A f(x+s)-B f(x)$ of the two-window mixture cannot change from negative back to positive when $0\le A\le B$. Sliding-window summation preserves this sign property. At the target degree choose $A=a_{d-s}+a_d$ and $B=a_d+a_{d+s}$. The hypothesis gives the required ordering. The weighted two-term comparisons then combine by balancing positive and negative summands at this tilt. Expanding the resulting inequality yields the theorem. On the falling side this choice can reverse the ordering, which is why the argument gives a one-sided conclusion.

## Formal statements

The original coefficient recurrences (12) and (14) are represented by `FirstColumn.sb` and `StirlingRecurrence.cb`. In `StirlingRecurrence.coeff`, true selects the first kind and false selects the second. The integer degree convention includes both zero-padded ends.

| Declaration | Mathematical scope |
| --- | --- |
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
