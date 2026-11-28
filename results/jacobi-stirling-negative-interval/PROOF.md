# The sharp negative parameter range for Jacobi–Stirling diagonal numerators

For real $u$, let $J(N,n;u)$ be the second-kind Jacobi–Stirling numbers, with $J(0,0;u)=1$, $J(N,0;u)=0$ for $N>0$, zero outside $0\le n\le N$, and
\[
J(N,n;u)=J(N-1,n-1;u)+n(n+u)J(N-1,n;u)\qquad(N,n\ge1).
\]
For integer $k\ge1$, put
\[
G_k(x;u)=\sum_{n\ge0}J(n+k,n;u)x^n,\qquad
A_k(x;u)=(1-x)^{3k+1}G_k(x;u)=xF_k(x;u).
\]
Here $u$ is Lin and Zeng's $z$, and $A_k$ uses their numerator convention. [Lin–Zeng, (1.2), (2.1) and (2.6)](https://arxiv.org/html/1309.4237v2#S2)

**Theorem.** For a real $u<0$, every $A_k(\cdot;u)$, $k\ge1$, is real-rooted if and only if $u\ge-1-\sigma$, where $\sigma$ is the unique nonnegative zero of
\[
D(s)=6144-25600s-18176s^2-19200s^3-9344s^4-3520s^5-720s^6.
\]
One has $1/5<\sigma<21/100$. Below $-1-\sigma$, $A_2$ has a nonreal pair. For $-1-\sigma\le u<-1$, $F_k$ has degree $2k-1$. Its even-indexed members have only negative zeros, and its odd-indexed members have one zero in $(0,1)$ and all others negative. All these zeros are simple except that $F_2(\cdot;-1-\sigma)$ has one double negative zero.

## The recurrence and a root count

Write $\theta=x\,d/dx$. Summing the triangular recurrence along the diagonal gives $G_0=(1-x)^{-1}$ and $(1-x)G_k=\theta(\theta+u)G_{k-1}$. The first summand in the triangle contributes $xG_k$, and the second applies the multiplier $n(n+u)$ to the $n$-th coefficient of $G_{k-1}$. With
\[
U_{a,b}p=x(1-x)p'+(a+bx)p,
\]
one has
\[
(\theta+c)\frac{xp}{(1-x)^M}
=\frac{x}{(1-x)^{M+1}}U_{1+c,M-1-c}p.
\]
Consequently $F_1=(1+u)+(1-u)x$, and for $m\ge1$, with $M=3m+1$,
\[
F_{m+1}=U_{1,M}U_{1+u,3m-u}F_m.
\]
In particular $\deg F_m\le2m-1$, $F_m(0)=(1+u)^m$, and $F_m(1)>0$, since $F_1(1)=2$ and each step multiplies the value at $1$ by $M(M+1)$. For $u<-1$, both operators increase degree by one and preserve the sign of the leading coefficient. Indeed, for an input of degree $d$, the new top coefficient is $b-d$ times the old one. In the inner operator $3m-u>2m-1$, and in the outer operator $M>2m$. Thus all $F_m$ have degree $2m-1$ and positive leading coefficient for $u<-1$.

We use the following negative-root count. Suppose $p$ is a nonzero real polynomial of degree $d$ and $b>d$. If $p$ has $N>0$ negative roots counted with multiplicity, $U_{a,b}p$ has at least $N$ negative roots in the gaps up to the last negative root and at old negative roots. If also $a>0$ and $p(0)\ne0$, it has at least $N+1$ negative roots, where this second conclusion applies also to $N=0$.

To see this, write the distinct negative roots as $r_1<\cdots<r_j$ with multiplicities $m_i$, and put $E=\prod_i(x-r_i)^{m_i-1}$, $S=p/E$, $T=(U_{a,b}p)/E$. The derivative term gives a polynomial quotient with
\[
T(r_i)=m_i r_i(1-r_i)S'(r_i).
\]
The signs alternate at consecutive roots, so $T$ has a zero in each intervening gap. At $r_1$, the sign of $T$ equals the sign of $S$ to the left of $r_1$. At large negative $x$, $T$ has the opposite sign to $S$, since its degree is one higher and the leading coefficients have the same sign. There is a zero before $r_1$. The factor $E$ accounts for another $N-j$ roots. If $a>0$ and $p(0)\ne0$, then $T(0)=aS(0)$ has the opposite sign to $T(r_j)$, giving a further zero in the last gap. When $j=0$, $S$ has constant sign on the negative half-line including at zero, so the signs at large negative $x$ and at zero again give one zero of $T$. In either count each gap supplies a distinct root away from the retained roots, and an old negative root of multiplicity $m_i$ has multiplicity exactly $m_i-1$ in the output.

For $-1<u<0$, real-rootedness already follows from Lin and Zeng's Lemma 2.3. It also follows from this count because $F_1$ has a negative root, both operators have $a>0$, $b>d$, and neither vanishes at zero on a nonvanishing input there. At $u=1$, $F_1=2$, and the same count applies from that constant because the inner degree margin is at least $m>0$ and the outer one is positive. Thus $F_k(\cdot;1)$ has only simple negative zeros, with a nonzero constant allowed at $k=1$. The triangular recurrence gives $J(N,n;-1)=J(N-1,n-1;1)$ for $N\ge n\ge1$, since shifting $n$ to $n-1$ changes the weight from $n(n-1)$ to $(n-1)n$ and both boundaries agree. Hence $G_k(x;-1)=xG_k(x;1)$, and $A_k(x;-1)=xA_k(x;1)$. In particular zero has multiplicity exactly two in $A_k(x;-1)$.

## The second diagonal and the even-to-odd step

Put $u=-1-\epsilon$ for $\epsilon>0$. Substituting $F_1=-\epsilon+(2+\epsilon)x$ into the recurrence gives
\[
F_2=\epsilon^2+(4-10\epsilon)x+(24-3\epsilon^2)x^2+2(3+\epsilon)(2+\epsilon)x^3.
\]
For $ax^3+bx^2+cx+d$ the discriminant $b^2c^2-4ac^3-4b^3d-27a^2d^2+18abcd$ expands here to $D(\epsilon)$. This polynomial is strictly decreasing on $[0,\infty)$, with $D(1/5)>0>D(21/100)$. For $\epsilon>\sigma$, the cubic has precisely one real zero and a nonreal pair. For $0<\epsilon<\sigma$, it has three distinct real zeros. At $\epsilon=\sigma$ the repeated root is real, because a repeated nonreal root would have a repeated conjugate, requiring degree at least four. The third root is then real. All coefficients of $F_2$ are positive for $0<\epsilon\le\sigma$, so these real zeros are negative. The repeated root at $\sigma$ has multiplicity exactly two. Indeed for $\epsilon\le21/100$, $b>23$, $a<15$, $0<c<4$, so $b^2>3ac$, whereas a triple root would give equality. Also $F_1$ has its single zero in $(0,1)$.

Take $0<\epsilon\le\sigma$, set $p=F_m$ and $q=U_{-\epsilon,M+\epsilon}p$, and suppose $m$ is even and all $d=2m-1$ roots of $p$ are negative. The negative-root count gives $d$ negative roots of $q$, counted with multiplicity, and $q(0)=-\epsilon p(0)<0<q(1)=Mp(1)$ supplies one more in $(0,1)$. These account for its degree $d+1$. If the negative roots of $p$ are simple or include just the double root of $F_2$, all roots of $q$ are simple, by the location and multiplicity in the count. The operator $U_{1,M}$ supplies one more negative root by its last-gap sign. At the positive zero $r$ of $q$, $q'(r)>0$ because the zero is simple and $q$ passes from negative to positive there. Thus $U_{1,M}q(r)>0$ while $U_{1,M}q(0)<0$. This supplies a zero in $(0,r)$, accounts for the full degree of $F_{m+1}$, and gives simplicity in particular for $F_3$ at the endpoint.

## The odd-to-even step

Suppose $m\ge3$ is odd, $p=F_m$ has one simple zero $r_+\in(0,1)$, and its other zeros $r_i$ are simple and negative. Write $q=U_{-\epsilon,M+\epsilon}p$ as above. We show that $q$ is negative somewhere between the largest negative zero of $p$ and zero. The first three coefficients of the series $G_m$ suffice.

Put $f_j=[x^j]G_m$, $w_i=i(i-1-\epsilon)$, $B=w_2=2(1-\epsilon)$, and $\alpha=\epsilon/B$. The diagonal recurrence gives
\[
[x^n]G_m=h_m(w_1,\ldots,w_n)
\]
for the complete homogeneous polynomial $h_m$. Indeed, both sides satisfy the recurrence $h_m(w_1,\ldots,w_n)=h_m(w_1,\ldots,w_{n-1})+w_n h_{m-1}(w_1,\ldots,w_n)$ with the same boundary values at $n=0$ and $m=0$. In particular $f_1=-\epsilon^m$. The alternating finite geometric sum for $f_2$ gives $f_2\ge (1-\alpha)B^m$ by grouping consecutive pairs of terms. For $f_3$, take absolute values in $h_m$, factor out $w_3^m$, and allow independently all nonnegative exponents of the first two weights. This gives
\[
|f_3|\le\frac{w_3^m}{(1-\epsilon/w_3)(1-B/w_3)}\le\frac{25}{16}w_3^m.
\]
Here $\epsilon\le\sigma<3/14$ implies $\alpha\le3/22$, $\epsilon/w_3\le1/25$, and $B/w_3\le1/3$. Also
\[
\frac{\epsilon w_3}{B^2}=\frac34\big((1-\epsilon)^{-2}-1\big)\le\frac{225}{484}.
\]

Let $g=f_2/\epsilon^m>0$, $L=1/r_+$, $s_i=-1/r_i>0$, and $S=\sum_i s_i$. Comparing the linear and quadratic coefficients in $p=(1-x)^M G_m/x$ with $p/p(0)=(1-Lx)\prod_i(1+s_i x)$ yields
\[
H:=L-S=g+M,\qquad
HS+\frac{S^2+\sum_i s_i^2}{2}
 =\frac{f_3}{\epsilon^m}-Mg-\binom M2.
\]
The right-hand side therefore bounds $gS$ from above, and in turn is at most $|f_3|/\epsilon^m$. It follows that
\[
\frac{S}{g}\le \frac{25}{16}\left(\frac{22}{19}\right)^2\left(\frac{225}{484}\right)^m<\frac29,
\qquad
\frac{M}{g}\le M\frac{22}{19}\left(\frac3{22}\right)^m<\frac1{30}.
\]
Both bounds decrease for integer $m\ge3$. For the second bound, the ratio of consecutive terms is $(3m+4)(3/22)/(3m+1)<1$. The displayed strict inequalities follow by substituting $m=3$.

Choose $t=3\epsilon/g>0$. Then $ts_i\le tS<1/7$ for all $i$, so $-t$ is to the right of every negative zero of $p$, and $p(-t)<0$. Set $h=H/g\ge1$, $s=S/g<2/9$, $c=3\epsilon<9/14$. Logarithmic differentiation of the factorization gives
\[
\frac{-t p'(-t)}{\epsilon p(-t)}
=3\left(\frac{h+s}{1+c(h+s)}-\sum_i\frac{s_i/g}{1-cs_i/g}\right)
\ge3\left(\frac{h+s}{1+c(h+s)}-\frac{s}{1-cs}\right).
\]
The inequality uses $1-cs_i/g\ge1-cs>0$ for every $i$. Since $h\ge1$, the difference in parentheses is at least
\[
\frac{1+s}{1+c(1+s)}-\frac{s}{1-cs}
=\frac{1-2cs(1+s)}{1+c-c^2s(1+s)}.
\]
The numerator is at least $1-2(1/7)(11/9)=41/63$, and the positive denominator is at most $1+c\le23/14$. Thus the logarithmic derivative expression is at least $3(41/63)/(23/14)=82/69>11/10$. Finally,
\[
\frac{q(-t)}{p(-t)}=(1+t)\left(-\epsilon-\frac{t p'(-t)}{p(-t)}\right)-Mt
>\frac{\epsilon}{10}-Mt>0,
\]
using $Mt=3\epsilon M/g<\epsilon/10$. This gives $q(-t)<0$.

At the last negative zero $r_i$ of $p$ the sign of $p'(r_i)$ is negative, since $p(0)<0$ and $r_i$ is simple. Therefore $q(r_i)>0$. Also $q(0)=\epsilon^{m+1}>0$. The sign at $-t$ supplies two distinct negative zeros in the last gap, in addition to the $d-1$ supplied up to that gap by the negative-root count. This accounts for the degree $d+1$ of $q$. All its zeros are simple and negative. The count for $U_{1,M}$ adds one negative zero and exhausts the degree again. This completes the parity induction, including $\epsilon=\sigma$, and proves the theorem.

## Two consequences at negative parameters

For each even $k\ge2$ and $-1-\sigma\le u<-1$, the numerator $A_k=xF_k$ has nonnegative coefficients, because $F_k$ has positive leading coefficient and all its zeros are negative. The series $G_k=A_k/(1-x)^{3k+1}$ then also has nonnegative coefficients. The fraction is in lowest terms since $A_k(1)>0$, so Lin and Zeng's Lemma 2.1 gives the Pólya frequency property for this individual second-kind diagonal. For example,
\[
25F_2(x;-6/5)=1+50x+597x^2+352x^3
\]
has signs $-,+,-,+$ at $-2,-1,-1/20,0$, giving a direct proof of three negative zeros. This contradicts an individual second-kind reading of the necessity direction of Lin and Zeng's Theorem 1.1. If that theorem is read as a joint Pólya frequency assertion for both kinds, this example concerns just one of its two sequences. The distinctness assertion as printed in Lemma 2.3 also has an exception at $u=-1$, where the zero at the origin is double as shown above. [Lin–Zeng, Theorem 1.1 and Lemmas 2.1 and 2.3](https://arxiv.org/html/1309.4237v2#S2)
