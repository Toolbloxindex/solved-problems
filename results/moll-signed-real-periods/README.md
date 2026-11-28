# Least periods of Moll’s signed arctangent companion sequence

## In brief

Victor Moll studied the real part of the running product $(1+i)(1+2i)\cdots(1+ni)$ with an alternating sign. His paper gives several periods modulo primes and proposes a formula based on the prime’s residue modulo eight. The exact period depends on the multiplicative order of $-2$ instead. For example, modulo 31 that order is 10, and the least period is 310 rather than the 930 proposed by the residue-class formula.

The proof compares a handful of terms near the initial index with the same terms one period later. For odd moduli, these comparisons recover the index modulo the modulus and both coordinates of the running Gaussian product. A full block then acts by a scalar. The result gives the least eventual period modulo every positive integer, and determines exactly when the pattern repeats from the start. The conjecture that the original tangent sums are nonintegral for every $n\ge5$ remains open.

## Exact statement

For $n\ge0$ set
$$
P_n=\prod_{k=0}^{n}(1+ik),\qquad f_n=(-1)^{n+1}\mathop{\rm Re}(P_n).
$$
This is the signed sequence in Moll’s Theorem 2.4. The extra factor at $k=0$ is one. For a positive integer $m$, write
$$
L(m)=\mathop{\rm lcm}_{p^e\parallel m,\ p\equiv 3\bmod 4}
         p^e\,\mathop{\rm ord}_{\mathbb F_p^\times}(-2),
$$
where $p^e\parallel m$ denotes an exact prime power and the empty lcm is 1. The least positive $t$ for which there is a cutoff $N$ satisfying $f_{n+t}\equiv f_n\pmod m$ for every $n\ge N$ is $L(m)$. For a positive $t$, equality holds for every $n\ge0$ precisely when every prime divisor of $m$ is $3\bmod4$ and $L(m)\mid t$. In particular, modulo 186 the least eventual period is 930 and there is no positive period from index zero. [Moll, Theorem 2.4 and §6](https://www.math.tulane.edu/~vhm/papers_html/xn-final.pdf)

## Proof

Put $S_n=(-1)^nP_n$, so $f_n=-\mathop{\rm Re}S_n$ and $S_{n+1}=-(1+i(n+1))S_n$.

**Recovering the shift.** Work modulo an odd $m$ and suppose $t$ is a period from zero of the signed real coordinate. At offset zero we have $S_t=1+iu$. Offsets one and two give $(t+1)u=0$ and $t(t+3)+(2t+3)u=0$. The first equation simplifies the second to $u=-t(t+3)$. Thus $F(t)=0$ for $F(X)=X(X+1)(X+3)$. Every nonnegative multiple of a period is a period, so $(m-1)t$ gives $F(-t)=0$. Adding yields $8t^2=0$, and oddness gives $t^2=0$. Substitution yields $3t=0$ and $u=0$. At offset four the difference of the real coordinates is $t^4+10t^3+29t^2+20t$. It follows that $20t=0$, so $3t=20t=0$ forces $t=0$ in $\mathbb Z/m\mathbb Z$. The state has also returned to its initial value $S_0=1$.

**Odd prime powers with $p\equiv3\pmod4$.** In the Gaussian ring modulo $p^e$, the signed multiplier for a block of length $p^e$ is
$$
C_e=-\prod_{k=0}^{p^e-1}(1+ik)=(-2)^{p^{e-1}}\pmod{p^e}.
$$
For example, the coefficientwise block identity of Cárdenas and Lluis gives the equality by specializing the polynomial variable to $i$. One can also obtain the prime case from $X^p-X=\prod_{k\in\mathbb F_p}(X+k)$. For $e>1$, group the factors by $k=j+a p^{e-1}$ with $0\le a<p$. The linear perturbation vanishes because $p$ divides $\sum_a a$, and all higher perturbations are multiples of $p^e$. This gives $C_e=C_{e-1}^p$ modulo $p^e$, with any integral lift on the right. Successive binomial lifts give the displayed formula. [Guillot–Ségalat, pp. 1 and 4](https://arxiv.org/pdf/1507.02834)

The order of $C_e$ equals $d=\mathop{\rm ord}_{\mathbb F_p^\times}(-2)$. Reduction modulo $p$ preserves that order because the exponent $p^{e-1}$ is coprime to $p-1$. Conversely, $(C_e)^d=1$ modulo $p^e$ follows by lifting $(-2)^d=1$ modulo $p$ using the binomial theorem. It follows that $p^e d$ is a period from zero. Any such period is a multiple of $p^e$ by the offset argument. For a shift $t=p^e k$, the same argument gives $1=S_t=C_e^k$, so $d\mid k$. Finally, a sequence periodic from zero has the same eventual and pure periods. An eventual comparison at any index can be shifted forward by a sufficiently large multiple of its known pure period.

**The other prime powers.** If $q$ is an odd prime congruent to $1\pmod4$, choose $r$ with $r^2=-1\pmod q$. A block of length $q$ contains both $r$ and $-r$. Their two factors multiply to $1+r^2$, so every such block supplies a factor $q$ to both Gaussian coordinates. The product is zero modulo $q^e$ after $e$ blocks. Modulo $2^e$, every odd $k$ supplies a factor $1+i$ and $2e$ such factors suffice, since $(1+i)^2=2i$. These local sequences are eventually zero and have no period from zero, since $f_0=-1$. The Chinese remainder theorem now gives both assertions, also when $m=1$.

## Prior work and scope

Moll’s preprint is dated 14 July 2012 and his publication list records the 2013 Scientia paper. His Theorem 6.1 gives the minimal period 171 modulo 19. Note 7.3 already records the smaller period 301 modulo 43, in conflict with the residue-only rule in Note 6.6. The block congruence was established by Cárdenas and Lluis (1987 conference, published 1989) and is given in Guillot and Ségalat’s Theorem 2.1 (2015). Amdeberhan, Medina and Moll (2008) bound a period of the norm sequence in Theorem 5.7. An October 2026 public report gives a prime-modulus period bound for Moll’s signed sequence using complete residue blocks. The offset argument above supplies the missing lower bound on the period of the real coordinate. The scope here includes prime powers and arbitrary composite moduli. Priority for the exact classification remains undetermined. [Moll’s bibliography](https://www.math.tulane.edu/~vhm/pap22.html) · [Amdeberhan–Medina–Moll](https://doi.org/10.1016/j.jnt.2007.05.008) · [October report](https://github.com/the-omega-institute/trureturing/issues/18633)

## Verification

`MollRigidity.gaussProd` omits the neutral factor and `MollRigidity.moll` applies the sign as $-((-1)^n\operatorname{Re} P_n)$. `EventualPeriod` quantifies over all indices above a single cutoff. `eventualLength` takes the lcm over distinct prime divisors, each with its exact factorization exponent. Theorems `MollRigidity.least_eventual_period` and `MollRigidity.pure_period_iff` record the two assertions above. An independent mathematical check reviewed the prime-power argument. A separate exact modular recurrence detects full state cycles and measures the output’s minimal periods on 168 moduli. The computation is a check on the formula. The general proof is deductive. Codex assisted with the mathematical development, checks and Lean formalization under Tomás Correia’s direction.

Run `python3 period_controls.py` to reproduce the literal recurrence comparisons. It prints period 310 modulo 31 and period 930 modulo 186, and reports agreement on 168 moduli.

To replay the proof, use Lean `leanprover/lean4:v4.37.0-rc1` and Mathlib commit `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. Build or fetch the Mathlib cache at that pin and set `MATHLIB` to its checkout. From a clean copy of the four Lean files, run

```sh
export ELAN_TOOLCHAIN=leanprover/lean4:v4.37.0-rc1
export LEAN_PATH="$PWD:$MATHLIB/.lake/build/lib/lean"
for lib in "$MATHLIB"/.lake/packages/*/.lake/build/lib/lean; do
  export LEAN_PATH="$LEAN_PATH:$lib"
done
for mod in MollRigidity MollPrime MollLift MollEventual; do
  lean -j1 -DwarningAsError=true -o "$mod.olean" "$mod.lean" || exit 1
done
cat > Audit.lean <<'LEAN'
import MollEventual
#check @MollRigidity.least_eventual_period
#check @MollRigidity.pure_period_iff
#print axioms MollRigidity.least_eventual_period
#print axioms MollRigidity.pure_period_iff
LEAN
lean -j1 -DwarningAsError=true Audit.lean
```

Both axiom audits print `[propext, Classical.choice, Quot.sound]`.
