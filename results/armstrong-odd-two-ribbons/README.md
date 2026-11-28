# Equal-length ribbons in Armstrong’s sum-two slice

## In brief

Drew Armstrong asks whether lattice points between successive coprime cuts can be partitioned into chains that visit one point at each successive rank and contain exactly $a$ points. At the cut where the coordinates sum to two, each point gives two occupied positions, with repetition allowed. Order those positions as a pair. Each chain starts by increasing the longer column and then alternates column increases. For example, when $a=7$ one seven-point chain runs from $(0,0)$ along $(0,j)$ through $(0,5)$ and then to $(1,5)$. The construction works at this cut for every odd $a\ge3$. Complementing the coordinates gives the reflected single slice. The general conjecture over all cuts remains open. [Armstrong’s paper](https://link.springer.com/article/10.1007/s00026-026-00819-9)

## What this settles

Armstrong’s Conjecture 10.2 holds at the cut $c=2$ and the reflected cut $c=(a-1)^2-2$ for every odd $a\ge3$, with the first cut checked in Lean and the reflected cut deduced in writing, while the general all-cut conjecture remains open.

## Why it matters

Focused contribution

A single geometric rule extends Armstrong’s small-parameter sum-two examples to every odd parameter and also gives their reflected partitions.

## Exact statement

For an integer $a\ge2$, Armstrong chooses $1\le c\le(a-1)^2$ with $\gcd(a,c)=1$ and takes the greatest integer $c'<c$ with $\gcd(a,c')=1$. Conjecture 10.2 requests a partition of the integer points $x\in\{0,\ldots,a-1\}^{a-1}$ with $c'<\sum_h x_h\le c$ into saturated chains of $a$ points. The order is componentwise comparison of suffix sums. Here $a=2n+1$ with $n>0$. The first pair of cuts is $(c',c)=(1,2)$. In the written reflection it is $((a-1)^2-3,(a-1)^2-2)$. [Definition 10.1 and Conjecture 10.2](https://link.springer.com/article/10.1007/s00026-026-00819-9)

## Prior work

Armstrong's 10 March 2024 preprint proves the $a=3$ case and records two ribbon partitions of the $a=5$ sum-two slice. The 28 April 2026 journal article gives $a=3,4$ and reports a computation for all $a=5$ cuts. It also reports standard partitions through $a=20$. Yonezu's 15 November 2026 preprint checks germ positivity through $a=32$. Davis's 24 November 2026 note proves the equivalence of germ positivity and existence of a Johnson statistic, uses box complementation to reflect germ counts and reports finite germ checks through $a=43$. Our result supplies equal-length saturated chains at the specified cuts. The dated search located no earlier uniform proof of this scope. Priority remains undetermined. [Armstrong’s first preprint](https://arxiv.org/html/2403.06318v1#S11) · [Journal](https://link.springer.com/article/10.1007/s00026-026-00819-9) · [Yonezu](https://doi.org/10.5281/zenodo.24223951) · [Davis](https://github.com/1337isnot1337/solved-conjectures/blob/ac77337e39db71307ef8393e5bb35b0d3ff52310/research/armstrong-johnson/NECESSITY.md)

## Verification

The complete argument is in [PROOF.md](PROOF.md). A separate Codex research session reconstructed the source coordinates, checked coverage and saturation by a different derivation, and tested the reflected cut. The mathematical review is in [REVIEW.md](REVIEW.md). Tomás Correia directed the project, with Codex assistance in the proof, formalization and review.

In `ArmstrongOddTwo.c2_ribbon_partition`, `Diagram` is a nonnegative weakly decreasing vector of $2n$ suffix sums with first coordinate 2. Successive differences, including the final difference to zero, recover the weights. Each difference is at most 2 and $2\le2n$, so the box bounds follow. The declaration gives membership at every indexed position, uniqueness of the position for every diagram and a single unit increase at each successor step. The reflection is proved in writing.

Replay with Lean `leanprover/lean4:v4.37.0-rc1` and Mathlib at `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. Build or fetch the mathlib cache at that pin, set `MATHLIB` to its checkout, and run in the directory containing the public Lean source.

```sh
export ELAN_TOOLCHAIN=leanprover/lean4:v4.37.0-rc1
export LEAN_PATH="$PWD:$MATHLIB/.lake/build/lib/lean"
for lib in "$MATHLIB"/.lake/packages/*/.lake/build/lib/lean; do
  export LEAN_PATH="$LEAN_PATH:$lib"
done
lean -j1 -DwarningAsError=true -o OddTwo.olean OddTwo.lean
cat > Audit.lean <<'LEAN'
import OddTwo
#check @ArmstrongOddTwo.c2_ribbon_partition
#print axioms ArmstrongOddTwo.c2_ribbon_partition
LEAN
lean -j1 -DwarningAsError=true Audit.lean
```

The expected axioms are `propext`, `Classical.choice` and `Quot.sound`. Run `python3 review_controls.py` for the illustrative finite checks. They finish with `PASS`.
