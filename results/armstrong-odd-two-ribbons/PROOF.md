# Ribbons in Armstrong's sum-two slice for every odd parameter

For every odd integer $a\ge3$, Conjecture 10.2 of Armstrong holds for $c=2$, with preceding coprime cut $c'=1$. In weight coordinates the slice consists of $x\in\{0,\ldots,a-1\}^{a-1}$ with $\sum_j x_j=2$. The tilted order compares all suffix sums and each ribbon has exactly $a$ points with consecutive tilted heights. The full conjecture covers every pair of coprime consecutive cuts, and the construction below also proves the reflected single slice. [Published source, Definition 10.1 and Conjecture 10.2](https://link.springer.com/article/10.1007/s00026-026-00819-9)

## Uniform construction

Write $a=2n+1$ with $n>0$, and put $m=2n$. Use zero-based indices $0,\ldots,m-1$. Encode a point by the ordered pair $0\le i\le j<m$ of its occupied indices counted with multiplicity. For example, $i=j$ means a two at that coordinate. Its tilted row vector has entries $\mathbf 1_{h\le i}+\mathbf 1_{h\le j}$. These are precisely the weakly decreasing nonnegative row vectors beginning with 2. The original box's restrictions on row differences are automatic because $m\ge2$. The tilted height is $i+j+2$. Increasing either index by one inside the triangle increases just one tilted coordinate by one.

For each $t=0,\ldots,n-1$, make a ribbon from ranks $r=2t,\ldots,2t+m$ of the column-index sum. At rank $r$ take the pair
\[
i=t+d(r),\qquad j=r-i,\qquad
d(r)=\max\left(0,\left\lfloor\frac{r+2-m}{2}\right\rfloor\right).
\]
The rank interval has $m+1=a$ points. The shift changes by zero or one at a step, so exactly one column index increases by one.

At each rank the admissible first indices of the triangle are the integers from $\max(0,r-m+1)$ through $\lfloor r/2\rfloor$. If $r<m$, the active chains have $t=0,\ldots,\lfloor r/2\rfloor$, with $d(r)=0$. If $r=m+2s+\epsilon$ with $\epsilon\in\{0,1\}$, the active chains have $t=s+\epsilon,\ldots,n-1$. They give first indices $2s+\epsilon+1,\ldots,n+s$, exactly the required interval. Each pair therefore appears once, and each adjacent step is saturated in the source's tilted order.

At $a=7$ the first ribbon runs through $(0,0),(0,1),\ldots,(0,5),(1,5)$. [Independent finite checks](review_controls.py)

The coordinate complement $x_j\mapsto m-x_j$ reverses the tilted order and sends sum 2 to $m^2-2$. Since $m^2\equiv1\pmod a$, this is also a single slice between consecutive coprime cuts $m^2-3$ and $m^2-2$. Reversing the complemented ribbons proves this matching reflected case in the written argument.
