# Independent review of Armstrong's sum-two ribbons

A separate Codex research session reconstructed the source model, checked the construction and its reflection, derived coverage by a different coordinate rule, and replayed the exact Lean declaration.

## Exact claim

Armstrong fixes an integer $a\ge2$. For each $1\le c\le(a-1)^2$ coprime to $a$, he takes the greatest integer $c'<c$ coprime to $a$ and asks for a partition of the integer box slice $c'<\sum_h x_h\le c$, $0\le x_h\le a-1$, into saturated chains of exactly $a$ points. The order compares all suffix sums. For $a=2n+1$ with $n>0$, write $m=2n$. At $c=2$, the predecessor is $1$, so the slice has exactly sum two. The reflected written claim takes $c=m^2-2$ and $c'=m^2-3$. [Journal article, Sections 7 and 10](https://link.springer.com/article/10.1007/s00026-026-00819-9)

In zero-based coordinates let $y_h=\sum_{k=h}^{m-1}x_k$ and $y_m=0$. Then $x_h=y_h-y_{h+1}$, including the last coordinate. The condition $y_0=2$ with a nonnegative weakly decreasing integral vector makes every difference lie in $[0,2]\subseteq[0,m]$. This establishes both directions of the equivalence between the source cut and Lean's `Diagram`. The last-coordinate bound follows directly from the weight box and is automatic here. One `UnitStep` is a strict cover even in the ambient lattice because an intermediate integral suffix vector would be forced to be one of its endpoints. The first conjunction of the Lean theorem guarantees membership, its unique-position clause supplies coverage and disjointness within and across all ribbons, and the final conjunction checks each adjacency in a ribbon of $m+1$ positions.

## Closest prior work

Armstrong's first preprint (10 March 2024) proves the $a=3$ case and explicitly records two partitions of the $a=5$, $c=2$ slice. The journal article (28 April 2026) gives $a=3,4$ and computationally confirms all $a=5$ cuts, including the reflected case. The source's standard partitions through $a=20$ assert consecutive ranks without the comparability requirement. The elementary Gaussian-binomial identity for the pair ranks is $\sum_{0\le i\le j<m}q^{i+j}={m+1\brack 2}_q=[m+1]_q(1+q^2+\cdots+q^{m-2})$. It matches the required starts and lengths at the level of rank counts. [First preprint, Section 11](https://arxiv.org/html/2403.06318v1#S11) · [Journal, Sections 9–10](https://link.springer.com/article/10.1007/s00026-026-00819-9)

## Weakest step

A point with two units at the same coordinate maps to two equal positive columns. The thresholds $y_h\ge2$ and $y_h\ge1$ are nonempty initial segments with respective last indices $i\le j$. Their indicator sum recovers $y$, including when the two segments coincide or fill the whole index set. Conversely $x_h=\mathbf{1}_{h=i}+\mathbf{1}_{h=j}$, so the pair uses multiplicity and has a unique inverse.

The feasible first indices at rank $r=i+j$ are $\max(0,r-m+1),\ldots,\lfloor r/2\rfloor$. At $0\le r<m$, the saved offset is zero and exactly $0\le t\le\lfloor r/2\rfloor$ contribute. For $r=m+2s+\epsilon$ and $\epsilon\in\{0,1\}$, the lower bound on active labels is $\lceil(r-m)/2\rceil=s+\epsilon$, the upper bound is $n-1$, and the offset is $s+1$. The image runs from $2s+\epsilon+1$ to $n+s$. The offset jumps from zero to one at $m-1\to m$ and, thereafter, it jumps only from odd ranks to even ranks. The last even rank $2m-2$ is the singleton $(m-1,m-1)$. For $m\ge4$ the preceding odd rank is the singleton $(m-2,m-1)$. For $m=2$ it is the rank $m-1$, again with that same pair. Ordered endpoints also rule out increasing the left index at equal columns. The first rank is $(0,0)$.

For the reflection, coordinatewise complement $x_h\mapsto m-x_h$ changes each suffix to $m(m-h)-y_h$. It therefore reverses each unit step, which becomes a positive unit step after reversing the chain. The sum becomes $m^2-2$. Since $m^2\equiv1\pmod a$, the upper cut has residue $-1$ and the immediately preceding integer has residue $-2$. Both are coprime to odd $a$, so this is precisely the claimed single slice. At $a=3$ it coincides with the original cut.

## Independent check

Use a partition of the triangle by rows and differences, without first fixing ranks. Label $(i,j)$ by
$$
t=\min\left(i,n-1-\left\lfloor(j-i)/2\right\rfloor\right).
$$
The second entry of the minimum is nonnegative because $j-i\le m-1$. For a fixed $t$, put $d=m-2t-2$. The points with $i=t$ have $0\le j-i\le d+1$. They form a horizontal segment from $(t,t)$ to $(t,m-t-1)$ with $m-2t$ points. The points with $i>t$ have gap $d$ or $d+1$. At gap $d$ they have $t+1\le i\le2t+1$, and at gap $d+1$ they have $t+1\le i\le2t$. Starting at the segment's endpoint, alternate increasing $i$ and increasing $j$, ending at $(2t+1,m-1)$. This runs through all $2t+1$ remaining points in the fibre, so its total length is $m+1$. Each pair has a single label and each step adds one unit to one suffix coordinate. In the segment $r\le m-1$ and $i=t$. In the alternating tail the ranks are $m,m+1,\ldots,m+2t$, and the shorter index increases at its first step and every other step thereafter. Thus the fibre derivation recovers the saved construction.

I compared both constructions on every odd $a$ from 3 to 65, enumerated the literal weight box for $a=3,5,7$ on both cuts, checked suffix increments after reflection, and compared the rank histogram. At $a=7$, the middle ribbon is $(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)$. As a failed alternative, the cyclic adjacency orbit on two-subsets of a seven-cycle has pair ranks $0,2,4,6,8,10,5$ under the translation from pairs $(i,j)$ to subsets $\{i,j+1\}$. Its size agrees with the ribbon length, while the missing ranks preclude saturation. These controls support the exact proofs above.

The fresh warning-as-error replay uses Lean `leanprover/lean4:v4.37.0-rc1` and Mathlib commit `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. An importing file restates the conclusion with `Diagram` and `UnitStep` unfolded. The declaration `ArmstrongOddTwo.c2_ribbon_partition` has axioms `propext`, `Classical.choice` and `Quot.sound`. The reflected claim has the written proof above.

## Verdict

Pass for the exact tilted-coordinate Lean statement at $c=2$ and the written reflected corollary for every odd $a\ge3$. This is a focused contribution. The general all-cut statement remains open. Priority for the uniform result is undetermined.
