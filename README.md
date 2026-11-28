# A uniform lower bound on the transient length of the consecutive-231 stack map

For every n ≥ 8, some permutation of length n takes at least n + 3 passes of the consecutive-231 stack map to reach a periodic point.

Let f(n) be the maximum, over permutations of length n, of the number of passes before first entering the periodic set. The construction proves f(n) ≥ n + 3 for every n ≥ 8. The map reads its stack from the top. A prospective push that creates a consecutive 231 forces a pop. Its periodic points are exactly the permutations avoiding both classical patterns 132 and 231. [Map and periodic-set characterization](https://arxiv.org/abs/2008.12297)

## Construction

Begin with the eight-letter word (5,2,4,7,8,6,3,1). For length n, insert a gap of n − 8 larger ranks between the adjacent 7 and 8, reversing the base orientation for odd n. For n > 8, place the ranks between 9 and n − 1 of parity opposite to n in increasing order, then n, then the remaining ranks in decreasing order. The alternating flanks keep a peak among the eight low letters through the padding phase. At the end of that phase, projection to the eight low letters supplies eleven more passes of delay. The total lower bound is (n − 8) + 11.

The Lean declaration constructs a permutation of 1 through n and excludes membership in the periodic set at every time t < n + 3. The formalization and its review used AI assistance. [Projection and base case](OptionalProjection.lean) · [Construction and final theorem](AlternatingGap.lean)

## Scope and prior work

Seidel and Sun ask about the maximal transient length. Kai Yi gives a uniform lower bound of n − 1 and asks whether the maximum divided by n diverges. The bound here leaves that growth question open. Priority beyond the cited comparison remains undetermined. [Seidel and Sun, Question 4.3](https://arxiv.org/abs/2308.05868) · [Yi, Section 4](https://arxiv.org/abs/2604.18626)

## Reproduce

Use Lean 4.37.0-rc1 at 0b77e12952ad39077d80d8bd6b66d601f225c321 and Mathlib at 31ce06eaadf4a200c0e1407c5f10953cf606b8f8. From a built checkout of that Mathlib revision, copy both Lean files into a fresh directory and run the following there with MATHLIB set to the absolute checkout path.

```sh
export LEAN_PATH=".:$(cd "$MATHLIB" && lake env printenv LEAN_PATH)"
lean -DwarningAsError=true -o OptionalProjection.olean OptionalProjection.lean
lean -DwarningAsError=true -o AlternatingGap.olean AlternatingGap.lean
printf '%s\n' 'import AlternatingGap' '#print axioms SC231.consecutive231_max_delay_lower_bound' > Audit.lean
lean Audit.lean
```
