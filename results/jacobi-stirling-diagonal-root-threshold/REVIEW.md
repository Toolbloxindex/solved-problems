# Independent mathematical review

Independent AI mathematical review of the separately authored written proof.

## Exact claim

Use the source's second-kind Jacobi–Stirling triangle with weight (n(n+u)), including (J(0,0;u)=1) and zero entries off the triangle. For fixed real (uge0), every polynomial
[
 A_k(x;u)=(1-x)^{3k+1}sum_{nge0}J(n+k,n;u)x^nquad(kge1)
]
has only real zeros if and only if (ule
ho). Here (
ho=2+s_*), where (s_*) is the unique nonnegative zero of the shifted second-diagonal discriminant given in the proof. Above (
ho), the second diagonal has a nonreal conjugate pair. The proof separately gives the degree at every real (u) and supplies an exact counterexample to the positive-zero assertion in the source proof. [Lin–Zeng, §2](https://arxiv.org/html/1309.4237v2#S2)

## Closest prior work

Egge's Theorem 5.1 treats (u=1). Lin and Zeng's October 2013 revision gives the series recurrence, nonpositive roots on ([-1,1]) and an inversion identity. They study Pólya frequency, which requires nonpositive zeros for these numerators. The positive-zero counterexample concerns an auxiliary step in their proof. At that counterexample the nonreal pair itself rules out Pólya frequency. Gessel–Lin–Zeng's Conjecture 15 and the dated October 2026 Ma–Wang partial theorem concern individual parameter coefficients. Davis's nondefault research branch contains the related projective recurrence for these coefficients. I found no earlier statement of this specialized real-root threshold in those checked results or in the November 2026 weighted Euler transform preprint. [Egge, Theorem 5.1](https://www.ericegge.net/papers/lsperm.pdf) · [Lin–Zeng, §2](https://arxiv.org/html/1309.4237v2#S2) · [Gessel–Lin–Zeng, Conjecture 15](https://arxiv.org/pdf/1201.0622) · [Ma–Wang, §4](https://arxiv.org/html/2610.03111v1#S4) · [Davis, projective recurrence](https://github.com/1337isnot1337/solved-conjectures/blob/36f68ded87032c2bf085cf19554f789497762274/research/campaign-20261121/gessel-lin-zeng-followup.md) · [Weighted Euler transforms, Theorem 1.1](https://arxiv.org/html/2611.17839)

## Weakest step

The critical induction must span the degree drop at (u=2), the double root at (u=
ho) and the transition to (k=3). The weighted function vanishes at both infinities because (d-b<0). It vanishes at zero from the left because (a>0). The right interval needs only the limit at (+infty), together with the existing positive roots. A repeated root of multiplicity (h) contributes exactly (h-1) to the next polynomial, since the coefficient of its differentiated term at the root is nonzero. The gaps and retained roots exhaust degree (d+1). When (2le ule
ho<3), the quadratic or cubic (F_2) supplies the start and both degree margins are strict from (k=3).

## Independent check

I also checked the root-preservation step without the weighted Rolle argument. Divide (U_{a,b}p) by (x(1-x)p) on the outer intervals. If the distinct roots of (p) are (r_i) of multiplicities (h_i), the quotient is
[
 sum_irac{h_i}{x-r_i}+rac{a}{x}+rac{a+b}{1-x}.
]
Every pole contributed by a root has positive residue. The quotient tends to (+infty) to the right and to (-infty) to the left of such a pole. Its asymptote at either infinity is ((d-b)/x), and it tends to (-infty) at (0^{-}). These signs bracket one root in each negative gap, including the two ends, and in every gap between positive poles and beyond the last. When the negative poles are absent, the same signs bracket the sole negative root between (-infty) and zero. Restoring the (h_i-1) retained multiplicities yields (d+1) roots, so each gap contains exactly one simple root. This checks the repeated-root boundary as well as simple roots.

For the cubic I computed its first four series coefficients directly from the triangle, then multiplied by the binomial expansion of ((1-x)^7). This recovers the displayed cubic and the discriminant signs on both sides of the unique cutoff. The Taylor coefficients of (G_k) are nonnegative for (uge0), and the first coefficient is positive. This accounts for the entire interval (0<x<1). The endpoint operator multipliers check (F_k(0)) and (F_k(1)).

For the degree formula, the substitution (x=1/t) gives (	hetamapsto-eta) and ((1-x)^{-1}mapsto-t/(1-t)). The first nonzero coefficient of the reciprocal series is a single product in each of the two cases. With (uin{1,dots,k}), there is exactly one zero among the first (k+1) weights, so exactly one product of size (k) survives. This fixes the degree drop at one. The isolated exact controls check the two low-diagonal examples, the bracket for the cutoff and several further ranks. The identity (F_2(x;3)=4(x(x-3)^2+2x+4)) proves the claimed exclusion of positive zeros for every (xge0).

## Verdict

Passed as a written proof for the stated nonnegative-parameter threshold, the exact degree formula and the specified counterexample. The test computations are corroboration. This review makes no claim of a Lean formalization or priority beyond the checked sources.
