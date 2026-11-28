# A sharp real-root range for Jacobi–Stirling diagonal numerators

## In brief

The Jacobi–Stirling numbers form a triangular array controlled by a parameter \(u\). Each fixed diagonal has a generating series with a polynomial numerator. Lin and Zeng studied when the zeros are all nonpositive. Here the question is when every numerator has real zeros, allowing either sign.

The first diagonal already has a positive zero when \(u>1\). At \(u=2\) the second numerator still has only real zeros. As the parameter increases beyond \(2\), two positive zeros meet at \(\rho\) and then become a nonreal pair. The second diagonal determines the exact threshold. Below and at that threshold, a weighted derivative argument accounts for every zero on the two real intervals outside \([0,1]\) at each later step.

For nonnegative \(u\), the range is the closed interval from zero to the threshold \(\rho\), which lies between \(41/20\) and \(33/16\). The proof also supplies the exact degree at every real parameter and an example where a diagonal numerator has no positive zero despite \(u>1\).

## What this settles

For every nonnegative real parameter \(u\), all second-kind Jacobi–Stirling diagonal numerators of index \(k\ge1\) are real-rooted exactly when \(u\le\rho\), with the second diagonal already having nonreal zeros above \(\rho\) and the negative-parameter classification outside the scope of this proof.

## Why it matters

Substantial advance

This extends the known range for real zeros beyond the nonpositive-root range of Lin and Zeng and shows that checking the first two diagonals completely decides the all-diagonal question for nonnegative parameters.

## Prior work and scope

Lin and Zeng's Lemma 2.3 gives real, nonpositive zeros for parameters in \([-1,1]\), and their equation (2.6) supplies the series identity behind the induction. Egge had treated the Legendre parameter \(u=1\) in Theorem 5.1. The new part of the root classification is the exact signed-root interval beyond \(u=1\), with collision at its upper endpoint and failure beyond it. The two source assertions checked are the degree assertion in Lemma 2.2 and the positive-zero assertion in the proof of Theorem 1.1. [Lin–Zeng, §2](https://arxiv.org/html/1309.4237v2#S2) · [Egge, Theorem 5.1](https://www.ericegge.net/papers/lsperm.pdf)

Gessel–Lin–Zeng's Conjecture 15 concerns individual coefficient polynomials in the parameter. Ma and Wang's Theorem 2 settles several fixed deletion-count families of that conjecture. Davis's nondefault notes give a related projective recurrence and investigate common interlacing for those coefficient families. The interior fixed deletion-count cases of Conjecture 15 remain open in the checked sources. [Gessel–Lin–Zeng, Conjecture 15](https://arxiv.org/pdf/1201.0622) · [Ma–Wang, §4](https://arxiv.org/html/2610.03111v1#S4) · [Davis, transformed recurrence](https://github.com/1337isnot1337/solved-conjectures/blob/36f68ded87032c2bf085cf19554f789497762274/research/campaign-20261121/gessel-lin-zeng-followup.md)

## Proof

The proof was developed with AI assistance. The series recurrence, weighted Rolle argument, cubic discriminant and degree correction are in [PROOF.md](PROOF.md).
