# The sharp negative parameter range for Jacobi–Stirling diagonal numerators

## In brief

The second-kind Jacobi–Stirling numbers form a triangular array that depends on a real parameter \(u\). Each diagonal has a generating function whose numerator is a polynomial. The question is how far below zero \(u\) can go while every one of those polynomials still has only real zeros.

At \(u=-6/5\), all the diagonal numerators have real zeros. Apart from the factor \(x\), the second numerator has three negative zeros, one in each of the intervals cut out by \(-2,-1,-1/20,0\). The odd diagonals each have one positive zero. The proof uses the first three generating-series coefficients to control where two negative zeros appear at each odd-to-even step.

There is an exact cutoff between \(-121/100\) and \(-6/5\). The cutoff is included, even though two roots of the second numerator coincide there. At every more negative parameter the second numerator has a nonreal pair.

## What this settles

For every real \(u<0\), all second-kind Jacobi–Stirling diagonal numerators of index \(k\ge1\) are real-rooted exactly when \(u\ge-1-\sigma\), including the endpoint where \(\sigma\) is the unique nonnegative zero of the polynomial in the proof.

## Why it matters

Substantial advance

The result extends Lin and Zeng's nonpositive-root range to the exact negative cutoff for real zeros and shows that the second diagonal decides the question for the whole family.

## Source and scope

Lin and Zeng's Lemma 2.3 establishes real, nonpositive zeros on \([-1,1]\), and their equation (2.6) gives the differential recurrence. The new classification covers the second kind at negative parameters, including a range where odd diagonals have a positive zero. Its even diagonals supply Pólya frequency examples below \(-1\), and at \(u=-1\) the origin is a double zero of every positive-index numerator. [Lin–Zeng, §2](https://arxiv.org/html/1309.4237v2#S2)

Gessel, Lin and Zeng's Conjecture 15 concerns the polynomials obtained by extracting individual powers of the parameter. Ma and Wang prove five infinite families of that conjecture, and the cases with exponent \(4\le i\le k-3\) remain open in the sources checked here. [Gessel–Lin–Zeng, Conjecture 15](https://arxiv.org/pdf/1201.0622) · [Ma–Wang, Theorem 2](https://arxiv.org/html/2610.03111v1#S4) · [Nonnegative range](https://github.com/Toolbloxindex/solved-problems/tree/v1.14.0/results/jacobi-stirling-diagonal-root-threshold)

## Proof

The [written proof](PROOF.md) was developed with AI assistance. It gives the cubic threshold, establishes the locations of the zeros at every index, and checks the endpoint multiplicities.
