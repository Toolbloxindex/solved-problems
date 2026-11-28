# Strictly positive weights can break real-rootedness with four deletions

Use the alphabet \(\bar1<1<\bar2<2<\cdots<\bar k<k\), with two copies of each unbarred letter and one copy of each barred letter. For \(S\subseteq[k]\), remove the barred letters indexed by \(S\). An admissible word has only letters greater than \(j\) between the two copies of each unbarred \(j\). Let \(A_{k,S}(x)\) count these words by internal descents. Ma and Wang's Corollary 2 proves simple negative zeros for every nonzero nonnegative mixture at the deletion counts in \(\{1,2,3,k-2,k-1\}\cap[k]\). [Ma–Wang, §4](https://arxiv.org/html/2610.03111v1#S4)

At \(k=31\), put \(E=A_{31,\{1,2,3,4\}}\), \(F=A_{31,\{28,29,30,31\}}\) and \(A=\sum_{|S|=4}A_{31,S}\). Both \(P=E+900F\) and \(Q=A+10^6P\) have a nonreal zero. The weight of each of the 31,465 deletion sets in \(Q\) is 1 except for the first four labels (weight 1,000,001) and last four labels (weight 900,000,001).

## Reconstruction from the words

At a stage of length \(L\), insert a letter larger than every old letter, or insert two adjacent equal copies of such a letter as a block. A word with \(d\) internal descents has \(L+1\) gaps. Its \(d\) descent gaps and the terminal gap preserve \(d\), and its other \(L-d\) gaps increase \(d\) by one. The empty word has one gap, which preserves zero descents. The resulting polynomial is
\[
 D_L p=(1+Lx)p+x(1-x)p'.
\]
The two unbarred copies of the maximum label must be adjacent, so remove them and then its barred letter if present. Conversely, inserting the barred letter first and the adjacent pair second preserves all earlier pair conditions. Thus at each label \(j\) apply \(D_L\) and advance the length by 2 if \(j\in S\). Otherwise apply \(D_L\), then \(D_{L+1}\), and advance the length by 3. Start with \(1\) at length \(0\).

For the equal-weight sum, write \(p_{k,i}(n)=[u^i]\operatorname{JS}(n+k,n;u)\). The source gives
\[
 xA_{k,i}(x)=(1-x)^{3k-i+1}\sum_{n\ge0}p_{k,i}(n)x^n,\qquad
 A_{k,i}=\sum_{|S|=i}A_{k,S}.
\]
The factor \(x\) accounts for their final descent. The Jacobi–Stirling recurrence gives \(\operatorname{JS}(n+k,n;u)=h_k(j(j+u):1\le j\le n)\), where \(h_k\) is complete homogeneous. Adding a last variable \(v=n(n+u)\) updates \(h_r\) to the old \(h_r\) plus \(v\) times the new \(h_{r-1}\). The checker extracts coefficients through \(u^4\) and applies the binomial convolution. It also sums the gap recurrence over every four-deletion set and compares the two vectors. [Gessel–Lin–Zeng, equations (2.6), (2.10) and Theorem 2](https://arxiv.org/pdf/1201.0622)

## Exact arithmetic and conclusion

If \(p\) has only real roots \(r_1,\ldots,r_d\), the product rule away from its roots gives
\[
 p'(x)^2-p(x)p''(x)=p(x)^2\sum_{j=1}^d (x-r_j)^{-2}\ge0.
\]
Continuity gives the inequality at the roots, including repeated roots. The checker reconstructs both vectors and evaluates the first three Taylor coefficients at \(-23\) by the binomial theorem, using integer arithmetic. For \(P\) and \(Q\) the Laguerre difference \(p'(-23)^2-p(-23)p''(-23)\) is strictly negative. Both polynomials therefore have nonreal zeros, as do their multiples by \(x\). Reproduce with `python3 verify.py`.

Conjecture 15 concerns the equal-weight polynomial for every rank and deletion count. This certificate disproves the extension of Ma–Wang's weight quantifier to four deletions. The all-rank equal-weight case at four deletions and its sufficient comparison in their Remark 1 remain open. Davis's independent work gave weighted examples for other deletion counts and a large-rank obstruction that covers fixed counts of at least six when at least four barred labels are retained. Jadav's archive gives a separate obstruction to bivariate stability. [Gessel–Lin–Zeng, Conjecture 15](https://arxiv.org/pdf/1201.0622) · [Davis's nondefault branch](https://github.com/1337isnot1337/solved-conjectures/blob/e72101030bb48dfff3f8f47cc8e70953cb9df573/research/gessel-lin-zeng-descent-roots/COMMON-INTERLACING-BARRIER.md) · [Jadav's exact check](https://github.com/Atharvsinh-codez/conjectures/blob/8e5651a9842b42d8ef19fbae8d606d1ebdb2c2e0/gessel-lin-zeng/verify/verify_msg13.py)
