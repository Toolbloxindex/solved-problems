import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

namespace Graffiti392
open Finset Classical
noncomputable section
variable {n : Nat}
abbrev V (n : Nat) := Fin n

structure Graph (n : Nat) where
  adj : V n → V n → Prop
  symm : ∀ {x y}, adj x y → adj y x
  loopless : ∀ x, ¬adj x x

namespace Graph
variable (G : Graph n)
open Classical in
def nbr (x : V n) : Finset (V n) := univ.filter (G.adj x)

@[simp] theorem mem_nbr {x y : V n} : y ∈ G.nbr x ↔ G.adj x y := by classical simp [nbr]

def degree (x : V n) := (G.nbr x).card
def Connected := ∀ S : Finset (V n), S.Nonempty → (∃ y, y ∉ S) →
  ∃ x ∈ S, ∃ y ∉ S, G.adj x y

def minimum := univ.filter (fun x => decide (∀ y, G.degree x ≤ G.degree y))
def two := univ.filter (fun x => G.degree x = 2)
def twoNbr (x : V n) := G.nbr x ∩ G.two
def exceptional := univ.filter (fun x => (G.twoNbr x).card = 1)
def paid := G.minimum ∪ G.exceptional
def inside := G.two.filter (fun x => (G.twoNbr x).card = 2 ∧ x ∉ G.paid)
def fixed (x : V n) := G.degree x = 2 ∨ 0 < (G.twoNbr x).card

@[simp] theorem mem_minimum {x : V n} : x ∈ G.minimum ↔ ∀ y, G.degree x ≤ G.degree y := by
  classical simp [minimum]
@[simp] theorem mem_two {x : V n} : x ∈ G.two ↔ G.degree x = 2 := by simp [two]
@[simp] theorem mem_twoNbr {x y : V n} : y ∈ G.twoNbr x ↔ G.adj x y ∧ G.degree y = 2 := by
  simp [twoNbr]
@[simp] theorem mem_exceptional {x : V n} : x ∈ G.exceptional ↔ (G.twoNbr x).card = 1 := by
  simp [exceptional]
@[simp] theorem mem_paid {x : V n} : x ∈ G.paid ↔ x ∈ G.minimum ∨ x ∈ G.exceptional := by
  simp [paid]
@[simp] theorem mem_inside {x : V n} : x ∈ G.inside ↔ G.degree x = 2 ∧ (G.twoNbr x).card = 2 ∧ x ∉ G.paid := by
  simp [inside]

def TwoDominates (D : Finset (V n)) := ∀ x ∉ D, 2 ≤ (G.nbr x ∩ D).card

/-- Distinct representatives for vertex-disjoint edges. Each edge goes from its
unique representative in s to its distinct partner outside s. -/
def Matches (U s : Finset (V n)) := s ⊆ U ∧ ∃ f : s → V n, Function.Injective f ∧
  ∀ i, f i ∈ U ∧ f i ∉ s ∧ G.adj i (f i)

def gammaTwo := Nat.find (show ∃ k, ∃ D : Finset (V n), G.TwoDominates D ∧ D.card = k from
  ⟨_, univ, by simp [TwoDominates], rfl⟩)

private theorem matchingCandidates (U : Finset (V n)) :
    ∃ k, ∃ s : Finset (V n), G.Matches U s ∧ n - s.card = k :=
  ⟨_, ∅, by exact ⟨empty_subset _, fun i => i.val, Subtype.val_injective, by simp⟩, rfl⟩

def matching (U : Finset (V n)) := n - Nat.find (G.matchingCandidates U)

theorem gammaTwo_le {D : Finset (V n)} (h : G.TwoDominates D) : G.gammaTwo ≤ D.card :=
  Nat.find_min' _ ⟨D,h,rfl⟩

theorem gammaTwo_attained : ∃ D : Finset (V n), G.TwoDominates D ∧ D.card = G.gammaTwo :=
  Nat.find_spec (p := fun k => ∃ D : Finset (V n), G.TwoDominates D ∧ D.card = k) _

theorem le_matching {s U : Finset (V n)} (h : G.Matches U s) : s.card ≤ G.matching U := by
  have a : s.card ≤ n := by simpa using card_le_univ s
  have b := Nat.find_min' (G.matchingCandidates U) ⟨s,h,rfl⟩
  unfold matching
  omega

theorem matching_attained (U : Finset (V n)) :
    ∃ s : Finset (V n), G.Matches U s ∧ s.card = G.matching U := by
  obtain ⟨s,hm,he⟩ := Nat.find_spec (G.matchingCandidates U)
  have a : s.card ≤ n := by simpa using card_le_univ s
  refine ⟨s,hm,?_⟩
  unfold matching
  omega

/-- Pigeonhole gives a minimum-degree vertex in every nonempty finite graph. -/
theorem minimum_nonempty (h : Nonempty (V n)) : G.minimum.Nonempty := by
  classical
  obtain ⟨v⟩ := h
  let hp : ∃ d, ∃ x, G.degree x = d := ⟨_,v,rfl⟩
  obtain ⟨x,hx⟩ := Nat.find_spec hp
  exact ⟨x, G.mem_minimum.mpr (fun y => hx ▸ Nat.find_min' hp ⟨y,rfl⟩)⟩

theorem twoNbr_sub (x : V n) : G.twoNbr x ⊆ G.nbr x := inter_subset_left
theorem all_neighbors_two {x : V n} (h : G.degree x = 2) (t : (G.twoNbr x).card = 2) :
    G.twoNbr x = G.nbr x :=
  eq_of_subset_of_card_le (G.twoNbr_sub x) (by change G.degree x ≤ _; omega)

end Graph
end
end Graffiti392
