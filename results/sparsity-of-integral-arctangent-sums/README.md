# A sublogarithmic bound for integral arctangent-sum values

## In brief

Add the angles whose tangents are the integers from 1 to n, then take the tangent of the sum. Can the answer be an integer once n reaches five? Amdeberhan, Medina and Moll conjectured that it never is. This result limits how often an exception could occur. Among the first N indices, the count grows at most like the three-quarters power of the logarithm of N. The estimate still allows isolated exceptions.

## Statement and proof

Write $A_n+iB_n=\prod_{k=1}^n(1+ik)$. The count used in the Lean theorem is exactly the number of indices $5\le n\le N$ at which $A_n$ divides $B_n$. The real coordinate is nonzero in the integrality argument, and the slope is the tangent of the sum of angles. The final theorem bounds this count by $O((\log N)^{3/4})$ as $N$ tends to infinity.

The arithmetic argument gives a large absolute integer slope at any sufficiently late exceptional index. This confines the angle to a very short interval near a tangent pole. Determinant comparisons at translated pole labels restrict how many such indices can coexist. The counting inequality bounds the fourth power of their number by a constant times the cube of the logarithm. Taking fourth roots gives the stated exponent. [Final counting theorem](IntegralAsymptotic.lean) · [Arithmetic and analytic bridge](IntegralCount.lean)

## Prior work

Amdeberhan, Medina and Moll posed the all-index conjecture. Ken Ono established the logarithmic counting bound. The arithmetic height reduction has earlier public work in open-math-agents. The claim here is the three-quarters exponent; priority beyond this comparison is undetermined. [Original question](https://doi.org/10.1016/j.jnt.2007.05.008) · [Ono's bound](https://arxiv.org/abs/2607.05739) · [Earlier arithmetic reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/9e0e56b951b4126cd190fc6dc8216deb9bdbd112/reductions)

AI assistance was used to develop and review the proof.

## Replay

Use Lean 4.37.0-rc1 at 0b77e12952ad39077d80d8bd6b66d601f225c321 and Mathlib at 31ce06eaadf4a200c0e1407c5f10953cf606b8f8. From the result directory, set MATHLIB to a built checkout of the pinned Mathlib and use the matching compiler. The two supporting factorial and content lemmas are included at the start of GaussianContent.lean.

```sh
export LEAN_PATH=".:$(cd "$MATHLIB" && lake env printenv LEAN_PATH)"
for m in MollRigidity GaussianContent InertBlock MidpointDerivative MidpointPhase PoleAlgebra PoleCube PoleInverse PoleCount PoleBlock TangentBlocks GaussianAngle SlopeGrowth SlopeFactorial TangentCount IntegralCount IntegralAsymptotic; do lean -j1 -DwarningAsError=true -o "$m.olean" "$m.lean" || exit 1; done
printf '%s\n' 'import IntegralAsymptotic' '#print axioms ArctanPole.integral_count_isBigO' > Audit.lean
lean Audit.lean
```
