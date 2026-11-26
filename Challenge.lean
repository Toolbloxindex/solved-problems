module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod

@[expose] public section

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


def degree (x : V n) := (G.nbr x).card
def Connected := ∀ S : Finset (V n), S.Nonempty → (∃ y, y ∉ S) →
  ∃ x ∈ S, ∃ y ∉ S, G.adj x y

def minimum := univ.filter (fun x => decide (∀ y, G.degree x ≤ G.degree y))
def two := univ.filter (fun x => G.degree x = 2)
def twoNbr (x : V n) := G.nbr x ∩ G.two
def exceptional := univ.filter (fun x => (G.twoNbr x).card = 1)
def TwoDominates (D : Finset (V n)) := ∀ x ∉ D, 2 ≤ (G.nbr x ∩ D).card

/-- Distinct representatives for vertex-disjoint edges. Each edge goes from its
unique representative in s to its distinct partner outside s. -/
def Matches (U s : Finset (V n)) := s ⊆ U ∧ ∃ f : s → V n, Function.Injective f ∧
  ∀ i, f i ∈ U ∧ f i ∉ s ∧ G.adj i (f i)

def gammaTwo := Nat.find (show ∃ k, ∃ D : Finset (V n), G.TwoDominates D ∧ D.card = k from
  ⟨_, univ, by simp [TwoDominates], rfl⟩)

theorem matchingCandidates (U : Finset (V n)) :
    ∃ k, ∃ s : Finset (V n), G.Matches U s ∧ n - s.card = k :=
  ⟨_, ∅, by exact ⟨empty_subset _, fun i => i.val, Subtype.val_injective, by simp⟩, rfl⟩

def matching (U : Finset (V n)) := n - Nat.find (G.matchingCandidates U)


/-- The bound in Graffiti.pc 392b for all finite connected simple graphs of order greater than two. -/
theorem conjecture392b (hn : 2 < n) (hc : G.Connected) :
    G.gammaTwo ≤ G.matching (univ \ G.minimum) + G.minimum.card + G.exceptional.card := by
  sorry
end Graph
end
end Graffiti392
