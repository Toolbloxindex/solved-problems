# An upper bound for seven-cube caps with three full perpendicular layers

Let $S\subseteq\{0,1,\ldots,6\}^{3}$ have no three distinct points on a real affine line. If for every $a\in\{0,1,2\}$ there exists $h_a\in\{0,\ldots,6\}$ for which $\lvert\{p\in S:p_a=h_a\}\rvert=14$, then $\lvert S\rvert\le 86$.

The proof consists of the following reduction and the exact finite replay in [verify.py](verify.py) with [forest.json](forest.json).

## Geometry and the initial cases

Every coordinate line contains at most two points of a cap. A coordinate layer has seven rows of this kind, so it contains at most 14 points. If a cap satisfying the hypotheses has at least 87 points, keep the union of the three specified layers, whose size is at most 42, and enough other points to obtain a cap of size exactly 87. The specified layers still have size 14. Reflect each coordinate individually if its specified height exceeds three. Permute the coordinates to put the resulting heights in weakly increasing order. These maps preserve the cube, the point counts and Euclidean collinearity.

In a coordinate layer the two free coordinates $(u,v)$ are read in ascending axis order and a cell is represented by bit $7u+v$. The planar search below produces every 14-point mask on the full board. For each normalized height triple the checker joins three copies of this bank. It requires the two masks for each pair of layers to select identical points on their common line. This agreement is necessary, since the masks describe the exact intersections of a single cap with the layers. It also ensures that the union of the three masks gives exactly the chosen mask in each layer. Thus all normalized candidates occur among the enumerated roots.

For two grid points $p\ne q$, let $g$ be the positive greatest common divisor of the coordinates of $q-p$, and put $v=(q-p)/g$. Every integer point of their real line is $p+tv$ for an integer $t$. Indeed integer coefficients in a Bézout identity for the coordinates of $v$ recover $t$ as an integer linear combination of the coordinates of the displacement from $p$. Any point of the cube on this line satisfies $|t|\le 6$ since some coordinate of $v$ is nonzero. The checker computes the other grid points on every such line by stepping over these integers, omitting $p$ and $q$. The same rule works in the planar search.

At a root or a child let $F$ be the union of the exact layer masks already fixed. If a line through two distinct points of $F$ contains another point of $F$, the case is impossible. Otherwise form the set $A$ of grid sites outside the fixed layers and off all lines through pairs of $F$. Any possible completion lies between $F$ and $F\cup A$. For each axis the parallel lines partition the cube, so the sum over these lines $L$ of $\min(2,\lvert L\cap(F\cup A)\rvert)$ is an upper bound. The least of the three sums is the axis-line bound.

## Planar domains and layer sums

An exact planar domain with parameters $(k,U,R)$ consists of all size-$k$ planar caps $M$ with $R\subseteq M\subseteq U$. Here $R$ and $U$ are the projections into a single layer of $F$ and $F\cup A$, respectively. The checker computes a domain by initializing the chosen points to $R$ and choosing extra points row by row. Each row can add zero, one or two allowed points, subject to its remaining capacity of two points minus the required population of the row. A column with two chosen points cannot receive another. A point blocked by a pair already chosen cannot be added. When two points are chosen at once within a row, the checker also excludes a collinear triple involving both new points and an earlier point. After adding the new points it updates the blocked set for every new pair. The sum of the remaining row capacities, capped in each row by the available cell count, bounds the number of extra points still possible. Pruning at this bound preserves every completion. For each valid mask its intersection with each successive row provides the corresponding choice. Thus the search returns precisely the domain. The cached size-14 and size-13 searches enumerate the whole board for those sizes first, then filter the resulting banks by $R\subseteq M\subseteq U$.

Start with an upper bound of 14 per layer. If the exact domain at the current bound $k$ is empty, reduce that bound to $k-1$. The checker tests down through 11 at a root. Bounds in each direction add because the layers partition $S$, and if the least directional sum is below 87 the case is closed. The three fixed layers have exact size 14, so their bounds need never drop.

## Coverage at the remaining roots

For each root still live, the certificate names a further layer $j$, perpendicular to some axis $a$, and lists branches giving the exact mask in that layer. Let $b_i$ be the seven current layer bounds in direction $a$. A size-87 cap would give layer $j$ a population in the interval

$$\max\bigl(0,87-\textstyle\sum_{i\ne j}b_i\bigr)\ \le\ k\ \le\ b_j.$$

The checker constructs the union of the exact domains for every $k$ in this interval and compares it to the recorded mask list in increasing order of size and then numerical mask. This covers layers whose population falls below their ceiling when the directional sum exceeds 87.

In each branch the checker adds the mask to $F$, fixes the additional layer, and recomputes $A$. It then tests the axis-line bound. If this bound is at least 87, the old layer ceilings remain valid by restriction. The newly fixed layer gets its exact size, and the checker tightens the other bounds by exact domain tests through size 10, stopping as soon as the least directional sum is below 87. Each recorded terminal bound must agree with the computed one and be strictly below 87.

The replay generates 132 planar 14-point masks and 15,532 planar 13-point masks. It reconstructs 18,086 initial roots and verifies the 29 remaining records and all 249 required branches. The axis-line bounds close 113 branches. Updated layer bounds close the other 136. The checker rejects a missing root, an unused root or an incomplete branch list. Since every normalized size-87 case occurs and every required branch closes, the claimed bound follows.

## Source and nearest earlier result

The unrestricted problem is to determine $a(7)$, the maximum population of the seven-cube under the real no-three-collinear condition. Kudriashov's September 2026 paper gives a 73-point example and certifies exact maxima through side six. At side seven it excludes the one-axis ordered layer profile $(14,12,12,12,12,12,14)$, of total 88. The present theorem covers any three full perpendicular layers at arbitrary heights and uses total 87. The paper's 94-point example uses side eight. [Kudriashov, Sections 3.3 and 3.4](https://arxiv.org/html/2609.25133v1#S3)

The earlier case proof used the same perpendicular forest with separate exact C++ matching and Python geometry replays. The present certificate reconstructs the required root and branch coverage from the masks using only Python's standard library. Pór and Wood's 2007 three-dimensional bounds concern the growth of $a(n)$. The independent preprints by Agama and by Ghosal, Goenka and Keevash concern asymptotic lattice problems. [Pór and Wood](https://doi.org/10.1007/s00453-006-0158-9) · [Agama](https://arxiv.org/abs/2106.15621v10) · [Ghosal, Goenka and Keevash](https://arxiv.org/abs/2509.06935v1)
