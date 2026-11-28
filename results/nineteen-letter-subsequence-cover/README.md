# A positional proof for a 19-letter subsequence cover

## In brief

Pick one shorter word and try to cover every letter of abacadbabdcabcbadac with occurrences of it. Each occurrence may skip letters, and different occurrences may cover different positions. The three copies of d force an unexpectedly rigid choice: a covering word must use all three. That pins its four intervening and end pieces in place and forces the entire original word. This answers the authors’ request for a computer-free proof for this particular word.

## Argument

Number source positions from 1. The three `d`’s are at 6, 10 and 17. The pieces before, between and after them are `abaca`, `bab`, `cabcba`, and `ac`. The fixed word `W` has at least one and at most three `d`’s. Write `P` for its prefix before the first `d` and `R` for its suffix after the last `d`.

At 6 the marked `d` is the first in its embedding, so `P` is a subsequence of `abaca`. The independent marks 2 and 4 lie before every source `d`, so `P` contains the unique `b` and `c` allowed by `abaca`, in that order. At 17 the marked `d` is the last in its embedding, so `R` is a subsequence of `ac`. The independent marks 18 and 19 both belong to `R`, which forces `R = ac`.

With one `d`, position 15 (`b`) must belong to `P` since `R` has no `b`. The `c` in `P` would have to lie strictly between 15 and the selected `d`, which can only be at 17. Position 16 is `a`.

With two `d`’s write `W = P d Q d R`. Each row uses its own embedding while retaining the same `P`, `Q`, and `R`.

| Source mark | Restriction on its embedding | Consequence for the fixed word |
| --- | --- | --- |
| 7 (`b`) | If 7 belongs to `P`, its following `c` must precede the first selected `d`, which is at most 10. There is no `c` in between. `R` contains no `b`. The only source `d` before 7 is at 6. | Position 7 starts `Q`, since 6 and 7 are consecutive. Thus `Q` begins with `b`. |
| 11 (`c`) | The first selected `d` is at most 10. If 11 belongs to `R = ac`, there must be an `a` strictly between the second selected `d` and 11. The only possible second `d` before 11 is at 10. | Position 11 lies in `Q`, so `Q` has a `c`. This excludes the pair `(6,10)` in every embedding since its gap is `bab`. |
| 10 (`d`) | The pair must include 10, and `(6,10)` has been excluded. | The pair is `(10,17)`, so `Q` embeds in `cabcba`. Every embedding now has second `d` at 17, with first `d` at 6 or 10. |
| 15 (`b`) | Position 15 lies after the first `d` and before the second. The only source position between 15 and 17 is `a` at 16. | Every `c` of `Q` precedes its `b` at 15. Hence `Q` begins with `b` and contains `bcb`. |
| 12 (`a`) | Position 12 lies between the selected `d`’s, and the only `c` between the first selected `d` and 12 is at 11. | In `cabcba`, a subsequence starting with `b` and containing `bcb` is `bcb` or `bcba`, because both `b`’s and the sole `c` between them are required. The only possible `a` in these words follows `bcb`. After position 11 there is no `b` before 12. Thus neither word can hit 12. |

With three `d`’s every embedding uses all three in order. Each piece between them, including the two ends, must separately cover its source block. A letter occurring once in a source word must occur once in its cover, aligns with itself in every embedding, and splits the coverage condition on its two sides. This is the authors’ Observation 5.1. It proves `ac` and `bab` primitive and splits `abaca` first at `c` and then its `aba` at `b`. [Observation 5.1](https://arxiv.org/html/2509.05827v1#S5.SS1)

For `cabcba`, local positions 1 and 6 force any cover to start with `c` and end with `a`. An occurrence covering position 2 forces the prefix `ca`, and the cover has a `b` after this prefix because it must cover the source `b`’s. An occurrence using position 4 as the initial `c` would therefore require `ab` after 4, whereas the suffix there is `ba`. Thus there are two `c`’s. The `a` in the prefix `ca` differs from the final `a`, so there are two `a`’s. All embeddings now align both pairs. The `b` at local position 3 lies before the second `c` and the `b` at 5 lies after it. A single `b` in the fixed word cannot serve both, since its order relative to the second `c` is fixed. The cover therefore has all six letters of the source. Applying this to the four blocks gives `W = S`.

## Prior work and attribution

Charalampopoulos, Pissis, Radoszewski, Rytter, Waleń and Zuba already established the answer computationally. Their question asks for a paper proof. The written proof answers that question by tracking the positions of the letters. The Lean proof establishes the same conclusion. It uses the positional decomposition, then exhaustively checks the candidates in the `fewD` list and the sublists of the first three blocks by kernel reduction. Priority for the argument remains undetermined. [Original question](https://doi.org/10.1016/j.tcs.2025.115216)

AI assistance was used in developing and checking this proof.

## Reproduce

Run `python3 control.py` in this directory for the independent computation. To replay Lean, use Lean 4.37.0-rc1 at 0b77e12952ad39077d80d8bd6b66d601f225c321 and Mathlib at 31ce06eaadf4a200c0e1407c5f10953cf606b8f8. Set MATHLIB to its built checkout and use the pinned compiler.

```sh
export LEAN_PATH=".:$(cd "$MATHLIB" && lake env printenv LEAN_PATH)"
for m in WordSPrimitivity Replay; do lean -j1 -DwarningAsError=true -o "$m.olean" "$m.lean" || exit 1; done
printf "%s\n" "import Replay" "#print axioms WordSPrimitivityReplay.exact_claim" > Audit.lean
lean Audit.lean
```
