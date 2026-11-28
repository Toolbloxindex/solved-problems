# Moll’s signed Gaussian-product periods

The two theorems identify the least positive eventual period of Victor Moll’s signed sequence modulo every positive integer and characterize all positive periods from index zero. The sequence is defined using the original sign and the product over $0\le k\le n$. Modulo 31 the exact period is 310. The arctangent nonintegrality conjecture is a separate question. [Moll’s Theorem 2.4 and Notes 6.6 and 7.3](https://www.math.tulane.edu/~vhm/papers_html/xn-final.pdf)

`Challenge.lean` imports only Mathlib and states the definitions and both claims. The separately compiled `Solution.lean` proves them from the modular block and period rigidity arguments in the four supporting modules. The bridge accounts explicitly for the neutral factor at index zero and the sign convention.

With the toolchain given in `lean-toolchain`, run `lake exe cache get` and `lake build`. The deliberate holes in the Challenge produce warnings. The Solution has no holes. The Lake manifest pins Mathlib and its transitive dependencies. Comparator checks both theorems and their concrete definitions.
