# Independent mathematical review of the negative parameter threshold

Independent AI mathematical review of the separately authored written proof.

## Exact claim

For the second-kind Jacobi–Stirling recurrence with weight $n(n+u)$ and its triangular initial conditions, let $A_k(x;u)$ be the numerator of the series for $J(n+k,n;u)$ over $(1-x)^{3k+1}$. For each real $u<0$, all $A_k(\cdot;u)$ with $k\ge1$ have real roots exactly when $u\ge-1-\sigma$. The positive number $\sigma$ is the zero of the shifted rank-two discriminant specified in the proof, and $1/5<\sigma<21/100$. On the added flank $[-1-\sigma,-1)$, the reduced numerator $F_k=A_k/x$ has degree $2k-1$. Even indices have only negative zeros and odd indices have exactly one zero in $(0,1)$ with all remaining zeros negative. The only repeated zero of these reduced numerators is a double negative zero of $F_2$ at the threshold. Below the threshold $F_2$ has a nonreal pair. [Source recurrence and numerator](https://arxiv.org/html/1309.4237v2#S2)

## Closest prior work

Lin and Zeng's Lemma 2.3 gives real nonpositive zeros on $[-1,1]$ and their differential recurrence supplies the two operators. The public nonnegative theorem treats parameters where the inner operator has positive constant multiplier. Ma and Wang's 2026 result concerns fixed parameter coefficients with a different denominator. The recent weighted Euler-transform theorem has different preservation hypotheses. The dated comparison also checked Davis's public nondefault branch through 28 November. The ten added commits concern Erdős problems and polygon density. [Lin–Zeng, §2](https://arxiv.org/html/1309.4237v2#S2) · [Reviewed nonnegative range](https://github.com/Toolbloxindex/solved-problems/tree/v1.14.0/results/jacobi-stirling-diagonal-root-threshold) · [Ma–Wang, §4](https://arxiv.org/html/2610.03111v1#S4) · [Weighted Euler transforms](https://arxiv.org/html/2611.17839) · [Davis branch comparison](https://github.com/1337isnot1337/solved-conjectures/compare/36f68ded87032c2bf085cf19554f789497762274...91662ae57d693ee3a2bc8e44738c9a645a88db80)

## Weakest step

At odd $m\ge3$, the inner operator must gain two roots between the largest old negative root and zero. Its signs at both ends of that interval are positive. Write $p/p(0)=(1-Lx)\prod_i(1+s_i x)$, with $L>1$ and $s_i>0$. If $g=f_m(2)/\epsilon^m$, $M=3m+1$ and $S=\sum_i s_i$, the linear coefficient gives $L-S=g+M$. The quadratic coefficient gives
\[
 (g+M)S+(S^2+\sum_i s_i^2)/2=f_m(3)/\epsilon^m-Mg-\binom M2.
\]
In particular $gS\le f_m(3)/\epsilon^m$. The bound $S/g<1/4$ ensures that the choice $t=3\epsilon/g$ satisfies $ts_i<1$ for every old root. Logarithmic differentiation gives the quoted lower bound $3(70/101-14/47)>11/10$ on $-tp'(-t)/(\epsilon p(-t))$. The additional term $Mt$ is less than $\epsilon/10$ because $M/g<1/30$. This yields a strict negative value for the new polynomial strictly inside the required gap.

At the threshold the cubic discriminant vanishes. Its coefficients satisfy $b^2>3ac$, ruling out a triple root, and they are all positive, ruling out zero and positive roots. The inner operator retains the double negative root with multiplicity one. The other new roots lie in distinct gaps. This proves simplicity for every later diagonal at the threshold as well as in the open interval.

## Independent check

I checked the sign point without using reciprocal-root estimates. A second test scale is $t'=2\epsilon^{m+1}/((1-\epsilon)f_m(2))$. Pair the alternating powers of the sole negative weight in $h_m$ to bound the $n$-th coefficient by the complete homogeneous sum in the other $n-1$ weights. For $n=3$ use a two-weight geometric bound and for $n\ge4$ count its $\binom{m+n-2}{n-2}$ monomials. Normalizing the operator tail by $\epsilon^{m+1}$, the first bound is less than $4/5$, the second less than $1/9$, and the remaining ratios are less than $1/40$. The sum is less than $19/20$. The constant and linear terms of the inner operator's series at $-t'$ sum to $-\epsilon^{m+1}$. On the closed disk of radius $t'$, the nonconstant part of $G_m/x$ has magnitude less than $(117/154)\epsilon^m$. This certifies that $-t'$ is strictly to the right of all old negative roots. This approach uses the original series directly and works at the closed endpoint.

I also checked the exact $u=-6/5$, $k=2$ witness. The polynomial $1+50x+597x^2+352x^3$ has opposite signs on each successive pair of endpoints among $-2,-1,-1/20,0$. This yields all three negative roots. Since the denominator is a power of $1-x$ and the numerator has nonnegative coefficients, this individual second-kind diagonal is Pólya frequency by Lin–Zeng's criterion. A joint assertion about first and second kinds has a different scope. At $u=-1$, the shift $J(N,n;-1)=J(N-1,n-1;1)$ contributes an additional factor $x$ to $A_k$, giving the stated double zero at the origin.

## Verdict

Passed as a written proof of the sharp negative-parameter interval, the parity and multiplicity statements on the additional flank, and the stated Pólya-frequency and distinctness checks. The dated comparison found earlier recurrences and related results with different scope. The arithmetic replay and the independent series argument support the proof.
