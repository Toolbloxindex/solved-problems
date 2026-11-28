# A sharp real-root range for Jacobi–Stirling diagonal numerators

For real \(u\), let \(J(m,n;u)\) be the second-kind Jacobi–Stirling numbers, defined by \(J(0,0;u)=1\), zero entries outside \(0\le n\le m\) and \(J(m,0;u)=0\) for \(m>0\), and
\[
J(m,n;u)=J(m-1,n-1;u)+n(n+u)J(m-1,n;u)
\qquad(m,n\ge1).
\]
We use the parameter \(u=z\) and the same diagonal numerator \(A_k\) as Lin and Zeng. [Lin–Zeng, (1.2) and §2](https://arxiv.org/html/1309.4237v2#S2)

**Theorem.** Define \(A_k(x;u)=(1-x)^{3k+1}\sum_{n\ge0}J(n+k,n;u)x^n\), for integers \(k\ge1\). For real \(u\ge0\), every \(A_k(\cdot;u)\) has only real zeros if and only if \(u\le\rho\), where \(\rho=2+s_*\) and \(s_*\) is the unique nonnegative zero of
\[
D(s)=11376-198368s-274352s^2-164928s^3-53744s^4-9440s^5-720s^6.
\]
Here \(41/20<\rho<33/16\). For every \(u>\rho\), \(A_2(\cdot;u)\) has two nonreal zeros.

## Recurrence and absence of zeros between zero and one

Put \(G_k=\sum_{n\ge0}J(n+k,n;u)x^n\) and \(\theta=x\,d/dx\). Summing the defining recurrence along a diagonal for \(k\ge1\), the first summand contributes \(xG_k\) after shifting \(n\) down by one. The second contributes \(\theta(\theta+u)G_{k-1}\). Thus
\[
(1-x)G_k=\theta(\theta+u)G_{k-1},\qquad G_0=(1-x)^{-1}.
\]
This is the formal series version of Lin and Zeng's (2.6). Acting on \(G_0\) gives \(G_1=x((1+u)+(1-u)x)/(1-x)^4\). For integers \(k\ge1\) write \(G_k=xF_k/(1-x)^{3k+1}\), so \(A_k=xF_k\). With \(U_{a,b}p=x(1-x)p'+(a+bx)p\), the identity
\[
(\theta+c)\frac{xp}{(1-x)^m}
=\frac{x}{(1-x)^{m+1}}\,U_{1+c,m-1-c}p
\]
gives, for \(k\ge2\),
\[
F_k=U_{1,3k-2}\,U_{1+u,\,3k-3-u}F_{k-1}.
\]
This constructs the polynomials and bounds \(\deg F_k\le2k-1\). At \(x=0\), the operator multiplies by \(a\), so \(F_k(0)=(1+u)^k\). At \(x=1\), it multiplies by \(a+b\), giving \(F_1(1)=2\) and \(F_k(1)=(3k-2)(3k-1)F_{k-1}(1)>0\) for all real \(u\). For \(0<x<1\) and \(u\ge0\), the Taylor series of \(G_k\) converges by the rational formula and has nonnegative coefficients by the defining recurrence. Its coefficient at \(x\) is \((1+u)^k>0\). It follows that \(F_k>0\) throughout \([0,1]\) for \(u\ge0\).

## The two outer intervals

Let \(p\) be a nonzero real polynomial of degree \(d\) with all its zeros in \((-\infty,0)\cup(1,\infty)\). Suppose \(a>0\), \(a+b>0\) and \(b>d\). Then \(U_{a,b}p\) has degree \(d+1\), all of its zeros are in the same union, and the count in \((1,\infty)\), with multiplicity, stays the same.

To prove this, on each interval set
\[
w(x)=|x|^a|1-x|^{-(a+b)}p(x).
\]
Differentiation gives \(x(1-x)w'=|x|^a|1-x|^{-(a+b)}U_{a,b}p\). The function \(w\) tends to zero at each infinity since \(w(x)=O(|x|^{d-b})\), and it tends to zero at \(0\) from the left since \(a>0\). On any interval with two zero endpoint values, including these limits, \(w\) has a critical point in the interior. For an infinite endpoint, choose a point with nonzero value inside and finite points on both sides where the absolute value is smaller. An interior maximum of \(|w|\) on that compact interval gives \(w'=0\). The same argument works with a finite endpoint given by a one-sided limit.

If \(p\) has \(j\) distinct negative zeros, the gaps between them together with the two end gaps from \(-\infty\) and to \(0\) give \(j+1\) new negative zeros. When \(j=0\), this is a single gap from \(-\infty\) to \(0\). If \(p\) has \(\ell\) distinct zeros above \(1\), the gaps between them and the gap from the last to \(+\infty\) give \(\ell\) new zeros above \(1\). For \(\ell=0\) this count is zero. At an old zero \(r\) of multiplicity \(m\), the new multiplicity is exactly \(m-1\), because the derivative term has this order with nonzero multiplier \(r(1-r)\), and the other term vanishes to order at least \(m\). These counts total \(d+1\). The coefficient of \(x^{d+1}\) in \(U_{a,b}p\) is \((b-d)\) times the leading coefficient of \(p\), so all zeros have been accounted for. In particular each new zero is simple.

## The second diagonal and the sharp endpoint

For \(0\le u<2\), \(F_1=(1+u)+(1-u)x\) has one negative zero for \(u<1\), is a nonzero constant for \(u=1\), and has one zero above \(1\) for \(1<u<2\). At step \(k\ge2\) the first operator in the recurrence has \(a=1+u>0\), \(a+b=3k-2>0\), and \(b-\deg F_{k-1}\ge k-u\). The second has \(a=1\), \(a+b=3k-1\), and \(b\) exceeds its input degree by at least \(k\). Therefore the lemma propagates real-rootedness whenever \(k>u\).

Multiplying out the recurrence at \(k=2\) gives
\[
F_2(x;u)=(1+u)^2+(14+10u)x+(21-6u-3u^2)x^2+
2(2-u)(1-u)x^3.
\]
At \(u=2\) the quadratic \(9+34x-3x^2\) has a negative zero and a zero above \(1\), by its signs at \(0\), \(1\), and the two infinities. The lemma applies from \(k=3\).

For \(u>2\), write \(F_2=ax^3+bx^2+cx+d\). Its discriminant \(b^2c^2-4ac^3-4b^3d-27a^2d^2+18abcd\) is \(D(u-2)\) by expansion. The polynomial \(D\) is strictly decreasing on \([0,\infty)\), with \(D(1/20)>0>D(1/16)\). For \(2<u<\rho\) the discriminant is positive, giving three distinct real zeros. At \(u=\rho\) the repeated root is real, since a repeated nonreal root and its conjugate would require degree at least four. The third root is real as well. All these zeros belong to the outer intervals by positivity on \([0,1]\). Since \(\rho<3\), the lemma propagates this property from \(k=3\) throughout \(2<u\le\rho\). For \(u>\rho\) the negative discriminant gives precisely one real zero of the cubic and a pair of nonreal zeros. Multiplying by \(x\) to obtain \(A_k\) adds only the zero at the origin. This proves the theorem.

## Two checks on the source assertions

Lin and Zeng's Lemma 2.2 claims degree \(2k\) for \(A_k\) for all real \(u\ne1\). At \((k,u)=(2,2)\) the formula above gives \(A_2=x(9+34x-3x^2)\) of degree three. More generally the exact degree for \(k\ge1\) and real \(u\) is
\[
\deg A_k=
\begin{cases}
2k-1&\text{if }u\in\{1,\ldots,k\},\\
2k&\text{otherwise}.
\end{cases}
\]

To see this, put \(H_k(t)=G_k(1/t)\), expanded at \(t=0\), and \(\eta=t\,d/dt\). Inverting the series recurrence as an identity of rational functions gives
\[
H_0=-t/(1-t),\qquad H_k=-\frac{t}{1-t}\eta(\eta-u)H_{k-1}.
\]
For \(n\ge1\), the coefficient \(h_k(n)=[t^n]H_k\) satisfies \(h_k(1)=0\) for \(k\ge1\) and \(h_k(n+1)=h_k(n)-n(n-u)h_{k-1}(n)\). Thus \(h_k(n)=(-1)^{k+1}e_k(j(j-u):1\le j<n)\), where \(e_k\) is the elementary symmetric polynomial of degree \(k\). This follows by the recurrence for adjoining one variable, with \(e_0=1\) and \(e_k=0\) for fewer than \(k\) variables. The first nonzero coefficient occurs at \(n=k+1\) if \(u\notin\{1,\ldots,k\}\), since the single product of the first \(k\) weights is nonzero. For exceptional \(u\), it occurs at \(n=k+2\), since the single product of the \(k\) nonzero weights among the first \(k+1\) weights is nonzero. As \(H_k=t^{3k+1}A_k(1/t)/(t-1)^{3k+1}\), the order at zero is \(3k+1-\deg A_k\). This also gives \([x^{2k}]A_k=k!\prod_{j=1}^{k}(j-u)\) for every real \(u\). [Lin–Zeng, Lemmas 2.2 and 2.4](https://arxiv.org/html/1309.4237v2#S2)

The proof of Theorem 1.1 claims that for each real \(u>1\) and every integer \(k\ge1\), \(A_k\) has a positive zero. At \((k,u)=(2,3)\) the identity
\[
F_2(x;3)=16+44x-24x^2+4x^3=4\bigl(x(x-3)^2+2x+4\bigr)
\]
shows strict positivity for \(x\ge0\). Its discriminant is \(-690176\), so the two nonreal zeros still preclude the Pólya frequency property in this example. The simultaneous Pólya frequency condition on all second-kind diagonals already fails for \(u>1\) because \(A_1\) has a positive zero. [Lin–Zeng, proof of Theorem 1.1](https://arxiv.org/html/1309.4237v2#S2)
