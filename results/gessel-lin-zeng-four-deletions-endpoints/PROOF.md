# Growing endpoint ranges in Ma–Wang's comparison

## Statement

In Ma–Wang's normalization set \(n=k-2\), \(P_n=A_{n,0}\) and \(B_n=D_{3n-1}A_{n+1,4}\). An endpoint gap means a gap between consecutive zeros of \(P_n\), counted from the specified end. There are absolute constants \(c_1,c_2>0\) such that, for all sufficiently large \(n\), each of the first \(\lfloor c_1\sqrt{n/\log n}\rfloor\) gaps counted from zero and each of the first \(\lfloor c_2\log n\rfloor\) gaps counted from the most negative zero contains a simple negative zero of \(B_n\). The proof identifies the ordinal of those zeros. The growing middle range of Remark 1 remains open. [Ma–Wang, Remark 1](https://arxiv.org/html/2610.03111v1#S4)

## Source polynomials and series

The alphabet is \(\bar1<1<\bar2<2<\cdots<\bar k<k\), with one copy of each barred letter and two copies of each unbarred letter. For a size-\(i\) set \(S\subseteq[k]\), remove the barred letters indexed by \(S\). In an admissible word every letter between the copies of \(j\) must exceed \(j\). The reduced polynomial \(A_{k,i}\) counts internal descents in all these words, summed with equal weight over \(S\). Gessel–Lin–Zeng include one final descent, which multiplies their polynomial by \(x\). Ma–Wang Corollary 2 proves the three smaller deletion-count families and the cases of one or two retained barred letters. In Remark 1, \(D_L f=(1+Lx)f+x(1-x)f'\) and the comparison is \(D_{3k-7}A_{k-1,4}\prec A_{k-2,0}\). The degrees \(2n-1,2n-2\) used here follow from the source degree \(2k-i-1\) and the leading term of \(D_L\). [Ma–Wang, §4](https://arxiv.org/html/2610.03111v1#S4)

Write \(p_{r,i}(m)=[u^i]h_r(j(j+u):1\le j\le m)\) for \(m\ge1\). The numerator identities and \(xD_L f/(1-x)^{L+2}=(x\,d/dx)(xf/(1-x)^{L+1})\) give
\[
 \frac{P_n(x)}{(1-x)^{3n+1}}=\sum_{m\ge1}p_{n,0}(m)x^{m-1},\qquad
 \frac{B_n(x)}{(1-x)^{3n+1}}=\sum_{m\ge1}m p_{n+1,4}(m)x^{m-1}.
\]
In particular the two denominators coincide. [Gessel–Lin–Zeng, (2.6) and (2.10)](https://arxiv.org/pdf/1201.0622)

For a polynomial \(W\) of degree \(d\), write \(W^*(x)=x^dW(1/x)\). Exact reversed identities follow from
\[
 p_{r,i}(-M)=(-1)^{r+i}[u^i]e_r(j(j+u):1\le j\le M-1),\qquad M\ge1.
\]
Here the left side is the polynomial extension in the integer argument. To prove the identity, use the recurrence \(h_r(m)-h_r(m-1)=m(m+u)h_{r-1}(m)\) with \(h_0=1\) and \(h_r(0)=0\) for \(r>0\). By induction in \(r\) it defines polynomials in \(m\) via discrete summation. Run the recurrence backwards from \(m=0\) on the formal generating series in \(r\). At \(m=-M\) this gives \(\prod_{j=0}^{M-1}(1-sj(j-u))\), and coefficient extraction gives the formula.

For a polynomial sequence \(f(m)\) of degree at most \(L\), if its series for \(m\ge0\) is \(xW(x)/(1-x)^{L+1}\), then
\[
 \sum_{M\ge1}(-1)^L f(-M)x^M
   =\frac{x^{L-\deg W}W^*(x)}{(1-x)^{L+1}}.
\]
For example, expand each numerator monomial \(x^a\) in the binomial basis \(\binom{m-a+L}{L}\), and use \((-1)^L\binom{-M-a+L}{L}=\binom{M+a-1}{L}\). The degree bounds here follow from the source numerator and its denominator. Take \(L=3n\) for both \(W=P_n,B_n\). The reciprocal pivot series after removing \(x^{n+1}\) has coefficient
\[
 [x^m]\frac{P_n^*(x)}{(1-x)^{3n+1}}=((n+m)!)^2 e_m(1/j^2: j\le n+m).
\]
The reciprocal partner series after removing \(x^{n+2}\) has coefficient
\[
 [x^m]\frac{B_n^*(x)}{(1-x)^{3n+1}}
 = (n+2+m)((n+1+m)!)^2
 \sum_{\substack{J\subseteq[n+1+m]\\ |J|=m}}
 \left(\prod_{j\in J}j^{-2}\right)
 e_4(1/j:j\in[n+1+m]\setminus J).
\]
The prefactor \(n+2+m\) comes from multiplying the original sequence by its series index. In the backwards formula this adds one sign, which cancels the change of parity in the denominator exponent.

## Endpoint near zero

Put \(p_{r,i}(m)=[u^i]h_r(j(j+u):1\le j\le m)\), and let \(q_{r,i}(m)=\binom ri m^{2r-i}\). For \(i=0,4\) and \(r\ge i\), put
\[
 C_m=\prod_{h<m}(1-h^2/m^2)^{-1}=\frac{m^{2m-1}}{(2m-1)!}.
\]
We show the uniform estimates
\[
 \frac{p_{r,i}(m)}{C_m q_{r,i}(m)}
 =1+O\left(\frac{m\log(m+1)}r\right)\quad (1\le m\le r),
 \qquad
 \frac{p_{r,i}(m)}{C_m q_{r,i}(m)}\le C(1+m/r)^4 \quad (m\ge1)
\]
for \(r\ge8\). The constants are absolute.

For each \(1\le h<m\), take an independent geometric count \(X_h\) with \(\Pr(X_h=a)=(1-h^2/m^2)(h^2/m^2)^a\), \(a\ge0\). Let \(T=\sum X_h\) and \(\Delta=\sum_{h<m}(m/h-1)X_h\). Expand the complete homogeneous polynomial by its multiplicities. After division by \(C_m q_{r,i}(m)\), the expression is the expectation on \(T\le r\) of \(e_i/\binom ri\), where the \(r\) inputs to \(e_i\) consist of \(X_h\) copies of \(m/h\) and \(r-T\) copies of 1. In particular this integrand is at least 1, giving the lower bound \(1-\Pr(T>r)\). Since \(\mathbb E X_h=h^2/(m^2-h^2)\le m/(m-h)\), Markov's inequality gives \(\Pr(T>r)\le C m\log(m+1)/r\).

For \(i=4\) the integrand is at most
\[
 \frac{(r+\Delta)^4}{r(r-1)(r-2)(r-3)}.
\]
This follows by retaining just the distinct-index terms of the fourth power of the sum of the inputs. For a geometric variable of parameter \(q\) as above, differentiating the geometric series gives \(\mathbb E X^4\le24q/(1-q)^4\), so
\[
 \|(m/h-1)X_h\|_4\le C\sqrt{m/h},\qquad
 \|\Delta\|_4\le Cm .
\]
The second inequality follows by the triangle inequality and \(\sum_{h<m} h^{-1/2}\le2\sqrt m\). Hence the integral is at most \((1+O(1/r))(1+Cm/r)^4\). For \(i=0\) it is at most 1. These upper and lower estimates give both assertions, including \(m=1\), where the two sums of variables are empty.

For the pivot, its power series after division by \((1-x)^{3n+1}\) has \(m\)-th coefficient \(c_P(m)=p_{n,0}(m)\) at \(x^{m-1}\). For the partner the coefficient is \(c_B(m)=m p_{n+1,4}(m)\). For either series write \(c(m)\) and \(\lambda_j=c(j)/c(j+1)\). The estimates give, uniformly up to \(j+1\le c_1\sqrt{n/\log n}+2\),
\[
 \lambda_j=
 \frac{C_j}{C_{j+1}}\left(\frac{j}{j+1}\right)^b
 \left(1+O\left(\frac{(j+1)\log(j+3)}n\right)\right),
\]
where \(b=2n\) for \(P\) and \(b=2n-1\) for \(B\). In the latter formula the common factor \(\binom{n+1}{4}\) cancels. The ratios \(C_{m+1}/C_m\) and their reciprocals are bounded by absolute constants, from the factorial formula.

On a circle \(|x|=s\lambda_j\) with \(s=1\pm 1/(8j)\), majorize the absolute \(m\)-th term by a constant times
\[
 M_m=C_m m^b(1+m/n)^4|x|^{m-1}
\]
with an additional common factor \(\binom{n+1}{4}\) for \(B\). For \(m\le j\) and \(m\ge2\), the leftward ratio \(M_{m-1}/M_m\) is at most \(C(1-1/j^2)^b\). Indeed \(((m-1)/m)^b\) is at most \(((j-1)/j)^b\) and \(1/|x|\le C((j+1)/j)^b\). For \(m\ge j+1\), the rightward ratio \(M_{m+1}/M_m\) is at most \(C(1-1/(j+1)^2)^b\), by combining \(((j+2)/(j+1))^b\) with the upper bound on \(|x|\). There is no left tail for \(j=1\). Both ratios are bounded by \(\eta=C\exp(-b/(j+1)^2)\). At \(m=j,j+1\) the majorant is at most a constant times \(c(j)|x|^{j-1}\), with the common factor included for \(B\). The two tails together are thus \(O(\eta)c(j)|x|^{j-1}\). Taking \(c_1\) small gives \(\eta=O(n^{-2})\) throughout the indicated range.

On the two circles the binomial \(c(j)x^{j-1}(1+x/\lambda_j)\) has modulus at least \(c(j)|x|^{j-1}/(8j)\). Rouché gives exactly \(j-1\) and \(j\) zeros respectively inside the circles. The one zero in the annulus is real by conjugation, negative by coefficient positivity, and has magnitude in \((1\pm1/(8j))\lambda_j\). It is the \(j\)-th zero from zero. The partner's \(\lambda_j\) divided by the pivot's is
\[
 \frac{j+1}{j}\left(1+O\left(\frac{(j+1)\log(j+3)}n\right)\right).
\]
By reducing \(c_1\), the relative error has modulus at most \(1/(8j)\). Consequently the partner's lower magnitude bound exceeds the pivot's upper one, since \((1-1/(8j))^2(1+1/j)>1+1/(8j)\). The ratio of consecutive pivot scales has lower bound \(C^{-1}\exp(2n/(j+1)^2)\), which tends to infinity uniformly in this range. The partner is therefore inside the claimed pivot gap.

## Endpoint at large negative magnitude

Put \(N=n+1\), \(H=H_N=\sum_{h\le N}1/h\) and \(E_N=e_4(1/h:h\le N)\). Let \(U_n,V_n\) denote \(P_n^*(z/n^2), B_n^*(z/n^2)\), normalized individually at zero, where \(W^*(x)=x^{\deg W}W(1/x)\). Define the finite products
\[
 \Phi_N(z)=\prod_{h\le N}(1+z/h^2),\qquad
 \Psi_N(z)=\frac{[t^4]\prod_{h\le N}(1+t/h+z/h^2)}{E_N}.
\]
For \(0\le R\le n\) we first prove
\[
 \|U_n-\Phi_N\|_R+\|V_n-\Psi_N\|_R
 \le \frac{C}{n}\exp(C\sqrt{R+1}), \qquad
 \|F\|_R=\sum_m |[z^m]F|R^m .
\]
The use of finite \(N\) and the second marked variable is important for this accuracy.

Let \(a_m=[z^m]\prod_{h\ge1}(1+z/h^2)=\pi^{2m}/(2m+1)!\), by Euler's sine product. For \(m\ge1\) the total weight of size-\(m\) sets \(J\) meeting \(\{h>M\}\), with weight \(w(J)=\prod_{h\in J}h^{-2}\), is at most \(a_{m-1}/M\). Also \(a_{m-1}\le C(m+1)^2a_m\). The reciprocal identities have raw coefficients after normalization and scaling as follows:
\[
 \begin{split}
 U:&\quad R_{P,m}\sum_{J\subseteq[n+m],\,|J|=m}w(J),\\
 V:&\quad R_{B,m}\sum_{J\subseteq[N+m],\,|J|=m}
                     w(J)\frac{e_4(1/h:h\in[N+m]\setminus J)}{E_N}.
 \end{split}
\]
Here \(R_{P,m}=\prod_{a=1}^m(1+a/n)^2\) and \(R_{B,m}=(1+m/(n+2))\prod_{a=2}^{m+1}(1+a/n)^2\). For \(m\) up to the corresponding numerator degree, which is at most \(2n\), the factors are at most \(C16^m\) and differ from 1 by at most \(C(m+1)^2 16^m/n\), by telescoping the product. The weight factor in the second sum is uniformly bounded, since \(e_4\le H_{N+m}^4/4!\), \(H_{N+m}=H+O(1)\) and \(E_N\asymp H^4\). For \(J\subseteq[N]\), adding \(m\) further variables changes the normalized weight by at most \(Cm/N\). In fact each added variable \(\alpha\) changes \(e_4\) by \(\alpha e_3\), and their sum is at most \(m/N\). These estimates bound the difference of each raw coefficient from its finite-product comparator by \(C(m+1)^2 16^m a_m/n\). The pivot's two cutoffs \(n+m\) and \(N\) are both at least \(n\), so the same tail bound applies. This also handles \(m=0\) since all constants equal 1.

Above the numerator truncation cutoffs (at least \(2n-2\)), the comparator coefficients are \(O(a_m)\), also bounded by the same majorant. Taking the weighted coefficient sum and absorbing the powers of \(m\) into a larger exponential in \(m\) gives a bound \(C\exp(C\sqrt{R+1})/n\), from the factorial formula for \(a_m\). The denominators of the two raw series are \((1-z/n^2)^{3n+1}\). Recovering each numerator multiplies by this factor before truncation. Its difference from 1 has norm at most \(C R/n\) for \(R\le n\), since \((1+R/n^2)^{3n+1}-1\le C R/n\). Both truncated raw series have norm at most \(C\exp(C\sqrt{R+1})\). Truncation reduces the norm, and the factor \(R\) can be absorbed by increasing \(C\) in the exponent. This proves the bound. [Euler's sine product](https://dlmf.nist.gov/4.22.E1)

For \(|z|=(j+1/2)^2\), put \(g_h(z)=h/(h^2+z)\). Then \(\Psi_N(z)=\Phi_N(z)e_4(g_h(z):h\le N)/E_N\). We will also use \(g_h\) on the segment \(|z+j^2|\le 5j/H\) of the real line, with \(h=j\) omitted. In either setting
\[
 \sum |g_h(z)-1/h|=O(\log(j+2)),\qquad
 \sum |g_h(z)|^2=O(1).
\]
To see this on the circle put \(a=j+1/2\), so \(|h^2+z|\ge |h-a|(h+a)\). On the segment put \(a=j\); for \(h\ne j\), \(|h^2+z|\ge |h-j|(h+j)/2\) when \(H\) is sufficiently large. For \(h\le a/2\) the sum of \(|g_h|\) is bounded and the sum of \(1/h\) is logarithmic. For \(a/2<h\le2a\) use \(|g_h|\le C/|h-a|\), which gives a logarithmic sum because all nonzero distances are at least \(1/2\). For \(h>2a\), \(|g_h-1/h|\le Ca^2/h^3\), a bounded sum. The square-sum bound follows directly from \(|g_h|\le C/|h-a|\). Omitting \(h=j\) costs at most \(1/j\) in comparison with the full harmonic sum.

For \(j\le c_2\log n+1\) this gives \(\sum g_h=H+O(\log(j+2))\), \(\sum|g_h|=O(H)\), and
\[
 e_s(g)=\frac{H^s}{s!}\left(1+O\left(\frac{\log(j+2)}H\right)\right)
 \quad(s=3,4).
\]
Indeed, the repeated-index terms of \((\sum g_h)^s\) have modulus bounded by \(\binom s2(\sum|g_h|^2)(\sum |g_h|)^{s-2}\). The same formula gives \(E_N=(H^4/24)(1+O(H^{-2}))\) using the undeformed variables. On the circle this yields \(|\Psi_N/\Phi_N-1|=o(1)\) uniformly. The minimum modulus of \(\Phi_N\) on the circle is at \(z=-(j+1/2)^2\), since each factor attains its minimum modulus there. Its value there has modulus at least \(1/(\pi(j+1/2))\) by the sine product, whose missing real tail factors lie in \((0,1)\). As long as \(c_2\) is sufficiently small, the absolute approximation errors above are \(o(1/(jH))\) uniformly on these circles and segments, which have \(|z|\le(j+1)^2\) for sufficiently large \(n\). Rouché therefore gives both \(U_n\) and \(V_n\) exactly \(j\) zeros by modulus inside the circle \(|z|=(j+1/2)^2\), including zero zeros for \(j=0\) by the same estimates with \(a=1/2\).

To locate real zeros, write \(z=-j^2+\delta\) and
\[
 K_{N,j}(z)=\prod_{\substack{h\le N\\h\ne j}}(1+z/h^2).
\]
Then \(\Phi_N(z)=K_{N,j}(z)\delta/j^2\) and
\[
 \Psi_N(z)=\frac{K_{N,j}(z)}{E_N}
      \left(\frac{\delta}{j^2}e_4(g_{\widehat j})
                  +\frac1j e_3(g_{\widehat j})\right).
\]
Here \(g_{\widehat j}\) is the list with \(h=j\) omitted. The product \(K_{N,j}\) has constant sign and modulus bounded below by an absolute positive constant on \(|\delta|\le5j/H\). For the infinite product, divide the sine product by \(\delta/j^2\). With \(s=\sqrt{j^2-\delta}\), use \(|\sin(\pi s)|\ge2|s-j|=2|\delta|/(s+j)\); at \(\delta=0\) use continuity. The omitted tail factors only decrease the absolute value. The pivot approximation thus has opposite signs of magnitude \(\gg1/(jH)\) at \(\delta=\pm j/H\). The partner approximation has opposite signs of that size at \(\delta=-5j/H,-3j/H\), since \(e_4(g_{\widehat j})/E_N=1+o(1)\) and \(e_3(g_{\widehat j})/E_N=(4+o(1))/H\). The same signs hold for \(U_n,V_n\). The brackets lie in their matching modulus annuli, establishing simplicity and the ordinals. In reciprocal coordinates the \(j\)-th partner zero is more negative than the \(j\)-th pivot zero and less negative than the \((j+1)\)-st pivot zero. Taking reciprocals yields the claimed gaps on the original axis.

## Relation to earlier methods

Durán used dominant terms to locate fixed-index zeros of classical Bell and Eulerian polynomials. Here the forward estimate is uniform in a growing window for the two specific Jacobi–Stirling polynomials. The reciprocal comparison uses a marked sine product and an independent growing window. The proof concerns the sufficient comparison in Ma–Wang's Remark 1. That remark also needs the middle gaps for the all-rank conclusion. [Durán, arXiv v2](https://arxiv.org/pdf/2404.03249) · [Ma–Wang, Remark 1](https://arxiv.org/html/2610.03111v1#S4)
