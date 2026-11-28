# One-edge closures with consecutive breaks in log-concavity

## In brief

Count the ways to pick k vertices of a graph with no edges between them. As k grows, those counts can go up to a single peak and then drop, yet still bend the wrong way compared with their neighbors. Can several such bends survive after one extra edge closes a tree into a cycle? Three explicit graphs show that they can. The 315-vertex example has three consecutive breaks and still has a single peak. This settles the existence question; minimal graph sizes remain open.

## Argument

The selected Lean theorem proves unimodality in the weak sense and proves a strict break at each displayed index. The independent Python check computes every coefficient, checks strict increase and decrease around each listed peak, and enumerates all the breaks. The unique peaks and exhaustive lists in this table come from that computation.

| Source tree | Vertices | Independence number | Unique peak | All breaks |
|---|---:|---:|---:|---|
| Bautista-Ramos, TG(2,5) | 70 | 37 | 21 | 34, 36 |
| Bautista-Ramos, Guillén-Galván and Gómez-Salgado, Corollary 4.13, m=16 | 312 | 164 | 95 | 162, 163 |
| Same authors, Corollary 4.14, m=13 | 315 | 164 | 97 | 161, 162, 163 |

## Graph and counting proof

Use a root with one exceptional neighbor carrying ℓ pendant two-edge arms. Attach m other neighbors to the root. Each of those neighbors has k children, and each child carries n pendant two-edge arms. Take (ℓ,n,k,m) respectively equal to (0,5,3,2), (3,4,2,16), and (7,5,2,13). In a single ordinary child’s set of arms, join the middle vertices of two distinct arms. This adds one previously absent edge between vertices with a common parent. Deleting it gives exactly the source tree, so the only cycle is the new triangle. [Original TG construction, Definition 1](https://arxiv.org/html/2511.00334v1#S2) · [Pattern construction, Definition 2.1 and Corollaries 4.13–4.14](https://arxiv.org/html/2603.14204v1#S4.SS4)

Write E=1+2x, F=Eⁿ and S=F+x(1+x)ⁿ. The latter is the polynomial of one child and its n arms, obtained by conditioning on the child. The edge insertion deletes exactly the independent sets selecting both marked middle vertices. Its local correction is D=x²Eⁿ⁻², since the other n−2 arms are free and both leaf tips of the marked arms are forbidden. This correction applies both when the child is available and when it is excluded.

For an ordinary neighbor of the root, its excluded and included contributions are H=Sᵏ and J=xFᵏ. In the marked branch they become H′=(S−D)Sᵏ⁻¹ and J′=x(F−D)Fᵏ⁻¹. For the exceptional branch let B=E^ℓ and A=B+x(1+x)^ℓ. Splitting on the central root now gives the full polynomial

$$I(x)=A(H+J)^{m-1}(H'+J')+xB H^{m-1}H'.$$

For the 315-vertex example the last five coefficients, in increasing degree, are 1021011657404661, 387842446878, 149265080, 136705 and 129. The three positive differences between the neighboring product and middle square are respectively 1979623123125064590996, 30739937593050590 and 566938295.

## Prior work and attribution

The tree constructions are due to Bautista-Ramos and to Bautista-Ramos, Guillén-Galván and Gómez-Salgado. Levit and Kadrawi’s Theorem 5.1 already treats single-break closures for other parameters. Here the additional edge preserves multiple breaks. The search found no earlier matching resolution; priority remains undetermined. [Problem 6.6](https://arxiv.org/html/2603.17114v1#S6)

AI assistance was used in developing and checking this proof.

## Reproduce

Run `python3 verify.py` in this directory for the independent computation. To replay Lean, use Lean 4.37.0-rc1 at 0b77e12952ad39077d80d8bd6b66d601f225c321 and Mathlib at 31ce06eaadf4a200c0e1407c5f10953cf606b8f8. Set MATHLIB to its built checkout and use the pinned compiler.

```sh
export LEAN_PATH=".:$(cd "$MATHLIB" && lake env printenv LEAN_PATH)"
for m in GraphCount GraphSource GraphDigits ClosureProblem; do lean -j1 -DwarningAsError=true -o "$m.olean" "$m.lean" || exit 1; done
printf "%s\n" "import ClosureProblem" "#print axioms UnicyclicClosure.problem_6_6" > Audit.lean
lean Audit.lean
```
