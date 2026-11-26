import Graph392
namespace Graffiti392.Graph
open Finset Classical
noncomputable section
variable {n : Nat} (G : Graph n)

def monoEdges (c : V n → Bool) : Finset (V n × V n) :=
  univ.filter (fun p => G.adj p.1 p.2 ∧ c p.1 = c p.2)
def same (c : V n → Bool) (v : V n) := (G.nbr v).filter (fun w => c v = c w)
def opp (c : V n → Bool) (v : V n) := (G.nbr v).filter (fun w => c v ≠ c w)
def rest (c : V n → Bool) (v : V n) :=
  (G.monoEdges c).filter (fun p => p.1 ≠ v ∧ p.2 ≠ v)
def flip (c : V n → Bool) (v w : V n) := if w = v then !(c w) else c w

private theorem count_edges (c : V n → Bool) (v : V n) :
    (G.monoEdges c).card = (G.rest c v).card + (G.same c v).card + (G.same c v).card := by
  classical
  let row := (G.same c v).image (fun w => (v,w))
  let col := (G.same c v).image (fun w => (w,v))
  have mr (x y : V n) : (x,y) ∈ row ↔ x = v ∧ y ∈ G.same c v := by
    simp [row, and_comm, eq_comm]
  have mc (x y : V n) : (x,y) ∈ col ↔ y = v ∧ x ∈ G.same c v := by
    simp [col, and_comm, eq_comm]
  have r (x y : V n) : (x,y) ∈ G.rest c v ↔
      (G.adj x y ∧ c x = c y) ∧ x ≠ v ∧ y ≠ v := by simp [rest,monoEdges]
  have s (x : V n) : x ∈ G.same c v ↔ G.adj v x ∧ c v = c x := by simp [same]
  have decomp : G.monoEdges c = G.rest c v ∪ row ∪ col := by
    ext ⟨x,y⟩
    simp only [monoEdges,mem_filter,mem_univ,true_and,mem_union,r,mr,mc,s]
    constructor
    · intro ⟨ha,hc⟩
      by_cases hx : x = v
      · subst x; exact Or.inl (Or.inr ⟨rfl,ha,hc⟩)
      by_cases hy : y = v
      · subst y; exact Or.inr ⟨rfl,G.symm ha,hc.symm⟩
      exact Or.inl (Or.inl ⟨⟨ha,hc⟩,hx,hy⟩)
    · rintro ((h|⟨rfl,h⟩)|⟨rfl,ha,hc⟩)
      · exact h.1
      · exact h
      · exact ⟨G.symm ha,hc.symm⟩
  have d1 : Disjoint (G.rest c v) row := by
    apply disjoint_left.mpr
    rintro ⟨x,y⟩ h k
    exact ((r x y).mp h).2.1 ((mr x y).mp k).1
  have d2 : Disjoint (G.rest c v ∪ row) col := by
    apply disjoint_left.mpr
    rintro ⟨x,y⟩ h k
    obtain ⟨rfl, hcol⟩ := (mc x y).mp k
    rcases mem_union.mp h with h|h
    · exact ((r x _).mp h).2.2 rfl
    · exact G.loopless _ ((s _).mp ((mr x _).mp h).2).1
  rw [decomp,card_union_of_disjoint d2,card_union_of_disjoint d1]
  simp only [row,col,card_image_of_injective _ (show Function.Injective
    (fun w : V n => (v,w)) from fun _ _ h => congrArg Prod.snd h),
    card_image_of_injective _ (show Function.Injective (fun w : V n => (w,v)) from
    fun _ _ h => congrArg Prod.fst h)]

theorem extend_cut (fixed : V n → Prop) (seed : V n → Bool) :
    ∃ c : V n → Bool, (∀ v, fixed v → c v = seed v) ∧
      ∀ v, ¬fixed v → (G.same c v).card ≤ (G.opp c v).card := by
  classical
  let P (k : Nat) := ∃ c : V n → Bool, (∀ v, fixed v → c v = seed v) ∧ (G.monoEdges c).card = k
  have hp : ∃ k, P k := ⟨_,seed,fun _ _ => rfl,rfl⟩
  obtain ⟨c,hc,hmin⟩ := Nat.find_spec hp
  refine ⟨c,hc,?_⟩
  intro v hv
  have keep : ∀ x, fixed x → flip c v x = seed x := by
    intro x hx
    have ne : x ≠ v := fun e => hv (e ▸ hx)
    simp [flip,ne,hc x hx]
  have low := Nat.find_min' hp (show P (G.monoEdges (flip c v)).card from ⟨_,keep,rfl⟩)
  have untouched : G.rest (flip c v) v = G.rest c v := by
    ext ⟨x,y⟩
    simp only [rest,monoEdges,mem_filter,mem_univ,true_and]
    by_cases hx : x = v <;> by_cases hy : y = v <;> simp [flip,hx,hy]
  have swap : G.same (flip c v) v = G.opp c v := by
    ext x
    by_cases hx : x = v
    · subst x; simp [same,opp,G.loopless]
    · simp only [same,opp,mem_filter,flip,ite_eq_right hx]
      cases c v <;> cases c x <;> simp
  have a := G.count_edges c v
  have b := G.count_edges (flip c v) v
  rw [untouched,swap] at b
  omega

theorem degree_split (c : V n → Bool) (x : V n) :
    (G.same c x).card + (G.opp c x).card = G.degree x := by
  exact card_filter_add_card_filter_not ..

end
end Graffiti392.Graph
