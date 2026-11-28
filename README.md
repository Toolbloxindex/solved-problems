# Sharp nonnegative Jacobi–Stirling root threshold

The statement uses Lin and Zeng's second-kind recurrence, parameter $z=u$, rank $k=m+1$ and denominator $(1-x)^{3k+1}$. The theorem gives the exact interval from zero to $\rho$ in which every positive rank has a numerator that splits over the reals. The rank-two discriminant defines $\rho\in(41/20,33/16)$. [Lin–Zeng, §2](https://arxiv.org/html/1309.4237v2#S2) · [Written theorem, v1.14.0](https://github.com/Toolbloxindex/solved-problems/tree/v1.14.0/results/jacobi-stirling-diagonal-root-threshold)

Challenge.lean defines the recurrence, the series and the threshold polynomial independently of the proof modules, leaving the theorem as the challenge. Solution.lean supplies the same three concrete definitions and proves the theorem from the exact source-series declaration. Comparator checks the concrete definitions transitively through the theorem type.

Use the pinned toolchain and manifest. Run the Mathlib cache acquisition and Lake build in this directory. The deliberate theorem placeholder in Challenge.lean produces a warning. The Solution audit uses propext, Classical.choice and Quot.sound.
