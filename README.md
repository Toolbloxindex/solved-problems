# Armstrong’s Catalan ribbon partition conjecture at a = 6

At a = 6, all nine slices of the fundamental box admit partitions into six-point saturated chains. The 1,296 ribbons cover all 7,776 points.

For each cut c between 1 and 25 coprime to 6, let p be the greatest integer below c coprime to 6. The slice consists of the five-tuples with coordinates between 0 and 5 whose coordinate sum lies in (p,c]. Each slice partitions into chains of six points in the tilted order (coordinatewise comparison of all suffix sums). Consecutive chain elements are covers even in the ambient integer lattice. The first cut uses p = −1. This proves the entire a = 6 instance of Conjecture 10.2. The conjecture for arbitrary a remains open. [Armstrong’s source, §10](https://arxiv.org/html/2403.06318v4#S10)

## Certificate

Five representative slices supply 778 explicit ribbons. Reflection supplies the other 518. In suffix coordinates each certified step increases one coordinate by one. There is no integer tuple strictly between its endpoints. The certificate checks also establish disjointness and coverage. The formal theorem uses signed integer coordinates and explicit box bounds. AI assistance was used in the construction, formalization and checks.

## Reproduce

Run the following from this directory. The Python verifier uses the standard library.

```sh
python3 check.py --complete 6 slice-*.json
```

Use Lean 4.37.0-rc1 (0b77e12952ad39077d80d8bd6b66d601f225c321) and a built Mathlib at 31ce06eaadf4a200c0e1407c5f10953cf606b8f8. Set MATHLIB to its absolute checkout path, select the pinned Lean compiler and run:

```sh
export LEAN_PATH=".:$(cd "$MATHLIB" && lake env printenv LEAN_PATH)"
for m in RibbonsData RibbonsVerifier RibbonsChecks Ribbons Replay; do
  lean -j1 -DwarningAsError=true -o "$m.olean" "$m.lean" || exit 1
done
printf '%s\n' 'import Replay' '#print axioms ArmstrongRibbons.SourceAudit.conjecture_10_2_integer_coordinates' > Audit.lean
lean Audit.lean
```

## Prior work

Armstrong reports constructions at a = 3 and 4 and computational confirmation at a = 5. His standard partitions through a = 20 impose a weaker condition. Germ positivity computations do not construct saturated chains. The literature review located no prior a = 6 ribbon partition; priority remains undetermined. [Armstrong](https://doi.org/10.1007/s00026-026-00819-9) · [Yonezu’s germ-positivity computations](https://doi.org/10.5281/zenodo.24223951)

The generated Lean checks store cumulative certificate masks using exact natural-number sums and shifts. The kernel checks the resulting integers against the supplied rows.
