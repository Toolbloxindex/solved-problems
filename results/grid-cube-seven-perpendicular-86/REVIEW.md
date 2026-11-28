# Independent mathematical and certificate review

Independent AI review of the separately authored exact checker and written proof.

## Exact claim

In the literal cube of integer coordinates from 0 to 6, every subset with no three distinct points on a real affine line and a layer of exactly 14 points perpendicular to each coordinate axis has at most 86 points. The three heights may differ. If there were a larger set, the union of the chosen full layers has at most 42 points, so one can shrink the set to size 87 while retaining those layers. The no-three-collinear condition is hereditary. [Primary source §3](https://arxiv.org/html/2609.25133v1#S3)

## Closest prior work

Kudriashov gives a 73-point witness and excludes a prescribed 88-point profile on one axis. The project already computed the conditional bound of 86 with C++ matching and separate geometric checks. The present result supplies a portable checker of that conditional proof. The unrestricted 86 bound has a distinct computational proof and a separate native Lean import. The asymptotic results of Pór and Wood, Agama, and Ghosal, Goenka and Keevash do not check this finite condition. [Kudriashov](https://arxiv.org/html/2609.25133v1#S3) · [Pór–Wood](https://doi.org/10.1007/s00453-006-0158-9) · [Agama](https://arxiv.org/abs/2106.15621v10) · [Ghosal–Goenka–Keevash](https://arxiv.org/abs/2509.06935v1)

## Weakest step

Coverage requires more than verifying the listed leaves. Coordinate reflections normalize each selected height to at most three, and a permutation orders them. The root generator requires equality of the two site masks on every shared line, so their union restricts back to the three full layers. It exhausts all such roots. The planar enumeration makes one choice of extra sites in each row. Its availability updates remove only sites on lines already holding two points or in full columns. With two simultaneous additions, checking mutual collinearity with each earlier point closes the only extra triple case. Remaining row capacities bound every later choice. Empty exact-size domains justify a one-point decrease because the relevant bound is already at that size. For the fourth chosen layer, the exact domains span every size from 87 minus the sum of the other six ceilings through its own ceiling. Checking solely the ceiling would omit valid smaller masks at a slack root.

## Independent check

I replayed the filed checker and certificate in a fresh directory with Python isolated mode and a 512 MiB virtual-memory limit. The 132 and 15,532 planar masks at sizes 14 and 13 led to 18,086 compatible roots. The checker closed all 249 children, with 113 axis-line and 136 layer-ceiling exclusions. It printed PASS in 7.88 seconds with 35,096 KiB peak RSS. In a separate exact mutation I recomputed the lower endpoint at a root whose three directional sums were 88. Its branch layer has ceiling 12 and lower endpoint 11. Deleting mask 6066660190214 from that required size-11 domain made the checker reject the certificate. The archived determinant and normalized-direction comparisons use distinct calculations for the layer geometry. A primitive lattice direction has a unit integer linear combination of its coordinates, so the integral enumeration tests every real-line obstruction.

## Verdict

Passed as a computer-assisted proof of the stated conditional bound. The isolated exact replay checks the complete coverage and rejects a missing required branch. The exact unrestricted maximum remains open.
