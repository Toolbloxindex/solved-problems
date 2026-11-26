import Graph392
import Mathlib.Combinatorics.Hall.Finite
namespace Graffiti392.Graph
open Finset Classical
noncomputable section
variable {n : Nat} (G : Graph n)

def cross (U : Finset (V n)) (c : V n → Bool) (x y : V n) :=
  x ∈ U ∧ y ∈ U ∧ G.adj x y ∧ c x ≠ c y

/-- Exchange each monochromatic subset of a smallest cover for its outside
neighbors. Hall then pairs every cover vertex with a distinct outside neighbor. -/
theorem crossing_cover (U : Finset (V n)) (c : V n → Bool) :
    ∃ s : Finset (V n), G.Matches U s ∧
      ∀ x y, G.cross U c x y → x ∈ s ∨ y ∈ s := by
  classical
  let B := G.cross U c
  let Covers (s : Finset (V n)) := ∀ x y, B x y → x ∈ s ∨ y ∈ s
  have rev {x y : V n} (h : B x y) : B y x :=
    ⟨h.2.1,h.1,G.symm h.2.2.1,Ne.symm h.2.2.2⟩
  let P (k : Nat) := ∃ s : Finset (V n), s ⊆ U ∧ Covers s ∧ s.card = k
  have existsCov : ∃ k, P k := ⟨_,U,fun _ h => h,fun _ _ e => .inl e.1,rfl⟩
  obtain ⟨s,sU,cov,scard⟩ := Nat.find_spec existsCov
  let side (a : Bool) := s.filter (fun x => c x = a)
  let targets (x : V n) := U.filter (fun y => y ∉ s ∧ B x y)
  have hall (a : Bool) : ∃ f : side a → V n, Function.Injective f ∧
      ∀ i : side a, f i ∈ targets i.val := by
    apply (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp
    intro q
    let X : Finset (V n) := q.image (fun i => i.val)
    let N := q.biUnion (fun i => targets i.val)
    have spec {x : V n} (hx : x ∈ X) : x ∈ s ∧ c x = a := by
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact mem_filter.mp i.property
    have xsub : X ⊆ s := fun _ h => (spec h).1
    have exposed {x y : V n} (h : B x y) (hx : x ∈ X) : y ∈ (s \ X) ∪ N := by
      have ny : y ∉ X := fun hy => h.2.2.2 ((spec hx).2.trans (spec hy).2.symm)
      by_cases ys : y ∈ s
      · exact mem_union_left _ (mem_sdiff.mpr ⟨ys,ny⟩)
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨h.2.1,ys,h⟩⟩)
    have cover' : Covers ((s \ X) ∪ N) := by
      intro x y e
      by_cases hx : x ∈ X
      · exact .inr (exposed e hx)
      by_cases hy : y ∈ X
      · exact .inl (exposed (rev e) hy)
      exact (cov _ _ e).imp (fun h => mem_union_left _ (mem_sdiff.mpr ⟨h,hx⟩))
        (fun h => mem_union_left _ (mem_sdiff.mpr ⟨h,hy⟩))
    have subsetU : (s \ X) ∪ N ⊆ U := by
      intro y hy
      rcases mem_union.mp hy with h|h
      · exact sU (mem_sdiff.mp h).1
      · obtain ⟨i,_,hh⟩ := mem_biUnion.mp h
        exact (mem_filter.mp hh).1
    have minimal := Nat.find_min' existsCov (show P ((s \ X) ∪ N).card from ⟨_,subsetU,cover',rfl⟩)
    have bound := card_union_le (s \ X) N
    have diff := card_sdiff_add_card_eq_card xsub
    have xeq : X.card = q.card := card_image_of_injective _ Subtype.val_injective
    change q.card ≤ N.card
    omega
  choose f inj target using hall
  let idx (i : s) : side (c i) := ⟨i.val,mem_filter.mpr ⟨i.property,rfl⟩⟩
  let mate (i : s) := f (c i) (idx i)
  have prop (i : s) : mate i ∈ U ∧ mate i ∉ s ∧ B i (mate i) :=
    mem_filter.mp (target _ (idx i))
  refine ⟨s,⟨sU,mate,?_,fun i => ⟨(prop i).1,(prop i).2.1,(prop i).2.2.2.2.1⟩⟩,cov⟩
  intro i j eq
  have hi := (prop i).2.2.2.2.2
  have hj := (prop j).2.2.2.2.2
  rw [eq] at hi
  have col : c i = c j := by
    cases h : c i <;> cases k : c j <;> cases l : c (mate j) <;> simp_all
  have member : i.val ∈ side (c j) := mem_filter.mpr ⟨i.property,col⟩
  have transport {a b : Bool} (e : a = b) (x : V n) (ha : x ∈ side a) (hb : x ∈ side b) :
      f b ⟨x,hb⟩ = f a ⟨x,ha⟩ := by subst b; rfl
  have value : f (c j) ⟨i.val,member⟩ = mate i := transport col i.val (idx i).property member
  have sij : (⟨i.val,member⟩ : side (c j)) = idx j := inj _ (value.trans eq)
  exact Subtype.ext (congrArg (fun z : side (c j) => z.val) sij)

end
end Graffiti392.Graph
