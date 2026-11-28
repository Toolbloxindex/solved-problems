import WordSPrimitivity

open List

namespace WordSPrimitivityReplay

private def target : List Char := "abacadbabdcabcbadac".toList

example : target.length = 19 := by decide

/-- Definition 1.1, with one strictly increasing map for each marked position. -/
def CoversByIndices (word : List Char) : Prop :=
  ∀ i : Fin target.length,
    ∃ f : Fin word.length → Fin target.length,
      StrictMono f ∧ (∀ j, word.get j = target.get (f j)) ∧ ∃ j, f j = i

theorem exact_claim (word : List Char) (h : CoversByIndices word) : word = target := by
  apply WordSPrimitivity.s_primitive
  intro i
  obtain ⟨f, increasing, letters, image⟩ := h i
  exact ⟨OrderEmbedding.ofStrictMono f increasing, letters, image⟩

theorem no_shorter_cover (word : List Char) (shorter : word.length < target.length) :
    ¬ CoversByIndices word := by
  intro h
  exact (Nat.lt_irrefl target.length) (exact_claim word h ▸ shorter)

example : CoversByIndices target := fun i => ⟨id, strictMono_id, fun _ => rfl, ⟨i, rfl⟩⟩

#print WordSPrimitivity.s_primitive
#print CoversByIndices
#print axioms exact_claim
#print axioms no_shorter_cover

end WordSPrimitivityReplay
