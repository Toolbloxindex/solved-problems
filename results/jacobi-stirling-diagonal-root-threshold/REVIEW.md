# Independent AI review

## Exact claim

The independent reviewer checked the equivalence between the literal second-kind Jacobi–Stirling numerator splitting at every positive rank and the fixed real parameter lying in the closed interval from zero to the upper cutoff. The published triangle convention, the denominator exponent and the rank shift were checked against equations (1.2) and (2.1). [Lin–Zeng](https://arxiv.org/html/1309.4237v2#S2)

## Closest prior work

Lin and Zeng gave the real nonpositive range. The nonnegative signed-root threshold was already proved in the v1.14.0 written release. The coefficient-extraction results of Ma and Wang treat different polynomials. [Written proof](https://github.com/Toolbloxindex/solved-problems/tree/v1.14.0/results/jacobi-stirling-diagonal-root-threshold) · [Ma–Wang](https://arxiv.org/html/2610.03111v1#S4)

## Weakest step

The independent review reconstructed the binomial-coefficient series normalization and checked the homogeneous inverse at the root −1, including repeated copies and the rank-two degree drops.

## Independent check

The reviewer obtained the projective recurrence directly from the differential equation for the source series. A positive-residue rational-function argument independently checked propagation. The reviewer also derived the rank-two cubic by the literal triangle and checked its discriminant with a Sylvester determinant.

## Verdict

The source mapping passed independent review. All eleven Lean source files matched the independent pinned replay, which imported the exact theorem and audited its standard axioms.
