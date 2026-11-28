module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

namespace ArctanPole
open Finset

def HasRectangle (S : Finset ℕ) (a h k : ℕ) : Prop :=
  a ∈ S ∧ a+h ∈ S ∧ a+k ∈ S ∧ a+h+k ∈ S

/-- Positive increments are allowed to coincide. -/
def CubeFree (S : Finset ℕ) : Prop :=
  ∀ a h k l, 0 < h → 0 < k → 0 < l → HasRectangle S a h k → ¬HasRectangle S (a+l) h k

def starts (S : Finset ℕ) (d : ℕ) := S.filter fun a => a+d ∈ S

private theorem same_gap {S : Finset ℕ} (H : CubeFree S) {h l : ℕ} (hh : 0 < h) (hl : 0 < l) :
    (starts (starts S l) h).card ≤ 1 := by
  apply card_le_one.mpr
  have ordered (a b : ℕ) (ha : a ∈ starts (starts S l) h) (hb : b ∈ starts (starts S l) h)
      (hab : a < b) : False := by
    simp only [starts, mem_filter] at ha hb
    have e : a+(b-a) = b := by omega
    have e' : a+h+(b-a) = b+h := by omega
    apply H a h (b-a) l hh (by omega) hl
    · exact ⟨ha.1.1, ha.2.1, by rw [e]; exact hb.1.1, by rw [e']; exact hb.2.1⟩
    · refine ⟨ha.1.2, ?_, ?_, ?_⟩
      · convert ha.2.2 using 1; omega
      · convert hb.1.2 using 1; omega
      · convert hb.2.2 using 1; omega
  intro a ha b hb
  rcases lt_trichotomy a b with hab|hab|hab
  · exact (ordered a b ha hb hab).elim
  · exact hab
  · exact (ordered b a hb ha hab).elim

def rising (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter fun p => p.1 < p.2

private theorem mem_rising {S : Finset ℕ} {a b : ℕ} :
    (a,b) ∈ rising S ↔ (a ∈ S ∧ b ∈ S) ∧ a < b := by simp [rising]

private theorem pair_count {S : Finset ℕ} {W B : ℕ} (hW : S ⊆ range W)
    (hB : ∀ d, 0 < d → (starts S d).card ≤ B) :
    S.card * S.card ≤ S.card + 2*W*B := by
  let f (p : ℕ × ℕ) := p.2 - p.1 - 1
  have maps : (↑(rising S) : Set (ℕ × ℕ)).MapsTo f (range W) := by
    rintro ⟨a,b⟩ hp
    obtain ⟨⟨_, hb⟩, _⟩ := mem_rising.mp hp
    have := mem_range.mp (hW hb)
    exact mem_range.mpr (by dsimp [f]; omega)
  have fiber (i : ℕ) : ((rising S).filter fun p => f p = i).card ≤ (starts S (i+1)).card := by
    apply card_le_card_of_injOn Prod.fst
    · rintro ⟨a,b⟩ hp
      obtain ⟨hab, hi⟩ := mem_filter.mp hp
      obtain ⟨⟨ha,hb⟩, hlt⟩ := mem_rising.mp hab
      have eq : a+(i+1) = b := by dsimp [f] at hi; omega
      exact mem_filter.mpr ⟨ha, eq ▸ hb⟩
    · rintro ⟨a,b⟩ hp ⟨a',b'⟩ hp' hyp
      obtain ⟨hab, hi⟩ := mem_filter.mp hp
      obtain ⟨hab', hi'⟩ := mem_filter.mp hp'
      have hl := (mem_rising.mp hab).2
      have hl' := (mem_rising.mp hab').2
      dsimp [f] at hi hi'
      dsimp at hyp
      simp only [Prod.mk.injEq]
      omega
  have rh : (rising S).card ≤ W*B := by
    calc
      _ = ∑ i ∈ range W, ((rising S).filter fun p => f p = i).card := card_eq_sum_card_fiberwise maps
      _ ≤ ∑ _i ∈ range W, B := sum_le_sum fun i _ => (fiber i).trans (hB (i+1) (by omega))
      _ = _ := by simp
  have sub : S.offDiag ⊆ rising S ∪ (rising S).image Prod.swap := by
    rintro ⟨a,b⟩ hp
    obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp hp
    apply mem_union.mpr
    rcases lt_or_gt_of_ne hab with h|h
    · exact Or.inl (mem_rising.mpr ⟨⟨ha,hb⟩, h⟩)
    · exact Or.inr (mem_image.mpr ⟨(b,a), mem_rising.mpr ⟨⟨hb,ha⟩, h⟩, rfl⟩)
  have count := ((card_le_card sub).trans (card_union_le ..)).trans
    (add_le_add rh ((card_image_le).trans rh))
  rw [offDiag_card] at count
  rw [Nat.mul_assoc]
  omega

/-- A positive-increment-cube-free subset of [0,W) has cardinality O(W^(3/4)). -/
theorem cube_free_count {S : Finset ℕ} {W : ℕ} (hW : S ⊆ range W) (H : CubeFree S) :
    S.card * S.card ≤ W + 2*W*Nat.sqrt (3*W) := by
  have hs : S.card ≤ W := (card_le_card hW).trans_eq (card_range W)
  apply le_trans (pair_count hW (B := Nat.sqrt (3*W)) ?_) (by omega)
  intro l hl
  have hT : starts S l ⊆ range W := (filter_subset ..).trans hW
  have hT' : (starts S l).card ≤ W := (card_le_card hT).trans_eq (card_range W)
  have hh := pair_count (B := 1) hT (fun _ hh => same_gap H hh hl)
  apply Nat.le_sqrt.mpr
  omega

end ArctanPole
