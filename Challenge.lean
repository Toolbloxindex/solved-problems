module

public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

open List

namespace WordSPrimitivityReplay

def target : List Char := "abacadbabdcabcbadac".toList

example : target.length = 19 := by decide

/-- Definition 1.1, with one strictly increasing map for each marked position. -/
def CoversByIndices (word : List Char) : Prop :=
  ∀ i : Fin target.length,
    ∃ f : Fin word.length → Fin target.length,
      StrictMono f ∧ (∀ j, word.get j = target.get (f j)) ∧ ∃ j, f j = i

theorem exact_claim (word : List Char) (h : CoversByIndices word) : word = target := by sorry

theorem no_shorter_cover (word : List Char) (shorter : word.length < target.length) :
    ¬ CoversByIndices word := by sorry

end WordSPrimitivityReplay
