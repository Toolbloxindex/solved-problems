# Equal-length ribbons in the sum-two slice

## In brief

Armstrong asks for partitions of certain lattice-point slices into chains of prescribed length. In the slice where the weights sum to two, a point is determined by two indices, allowing two copies of one index. For odd $a$, the ordered pairs of indices form a triangle. At each rank, assign the points from left to right to the active chains. Start and end the chains at alternate ranks so that each contains $a$ points. One of the two indices increases by one at each step, giving a saturated chain in the suffix-sum order.

## What this settles

Armstrong's Conjecture 10.2 holds at the cut $c=2$ for every odd $a\ge3$, and the Lean theorem covers this sum-two slice while the other cuts remain outside its scope.

## Why it matters

Focused contribution

The construction adds an odd-parameter family of equal-length partitions to Armstrong's all-cut results for $a=3,4,5$.

## Build and statement

With the toolchain in `lean-toolchain`, run `lake exe cache get` and `lake build`. The Challenge imports only Mathlib, gives the original source slice in tilted coordinates, and has one deliberate theorem hole. The Solution states the same definitions and proves the same theorem with no holes, using the construction in `OddTwo.lean`. The Lake manifest pins Mathlib and transitive dependencies. Comparator checks the partition theorem and both definitions in its statement. [Armstrong, Definition 10.1 and Conjecture 10.2](https://doi.org/10.1007/s00026-026-00819-9)
