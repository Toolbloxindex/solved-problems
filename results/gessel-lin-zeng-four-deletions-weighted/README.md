# A four-deletion obstruction for Jacobi–Stirling descent polynomials

## In brief

Start with two copies of every label and one barred copy of every label. After deleting four barred copies, count the allowed arrangements by descents, which are places where a letter is followed by a smaller one. This gives one polynomial for each deletion set. Gessel, Lin and Zeng ask whether the equal-weight sum always has real zeros. Ma and Wang proved that every nonnegative weighted sum works for several deletion counts, including one, two and three.

At rank 31, give extra weight to deleting the first four barred labels and to deleting the last four. Every deletion set still receives positive weight, but the resulting polynomial violates an inequality that every polynomial with only real zeros must satisfy. This example rules out a guarantee for all positive weights at four deletions. The all-rank claim for equal weights remains open. [Original conjecture](https://arxiv.org/pdf/1201.0622) · [Ma–Wang, §4](https://arxiv.org/html/2610.03111v1#S4)

## What this settles

At rank 31 and four barred deletions, a strictly positive integer weighting of all 31,465 deletion sets gives a Jacobi–Stirling descent polynomial with nonreal zeros, while Gessel–Lin–Zeng's all-rank equal-weight claim for four deletions remains open.

## Why it matters

Focused contribution

Ma and Wang's theorem for arbitrary weights at one, two and three deletions cannot extend to the next deletion count.

## Proof and replay

See [PROOF.md](PROOF.md) and the [independent AI review](REVIEW.md) for the construction and source normalization, and run `python3 verify.py` to reconstruct the polynomials and verify the two exact violations.
