module

public import GameValue
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Sum

@[expose] public section

namespace KaylesRays.Path
open LiteralKayles

def edge (i j : Nat) := decide (i+1=j ∨ j+1=i)

def score (n : Nat) : Nat := value edge (Finset.range n)

def translate (a : Nat) : Nat ↪ Nat :=
  ⟨fun k => a+k, by intro r s h; exact Nat.add_left_cancel h⟩

/-- Choosing the vertex numbered i leaves the prefix through i-2 and the
suffix starting at i+2, both with their actual path edges. -/
theorem option_value {n i : Nat} (hi : i<n) :
    value edge (drop edge (Finset.range n) i) =
      score (i-1) ^^^ score (n-i-2) := by
  let a := Finset.range (i-1)
  let b := (Finset.range (n-i-2)).map (translate (i+2))
  have memb (v : Nat) : v∈b ↔ i+2≤v ∧ v<n := by
    change v ∈ (Finset.range (n-i-2)).map (translate (i+2)) ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨k,hk,rfl⟩
      have kl := Finset.mem_range.mp hk
      change i+2≤i+2+k ∧ i+2+k<n
      omega
    · rintro ⟨vl,vr⟩
      exact ⟨v-(i+2),Finset.mem_range.mpr (by omega),by change i+2+(v-(i+2))=v; omega⟩
  have split : drop edge (Finset.range n) i = a ∪ b := by
    ext v
    simp only [drop,edge,Finset.mem_filter,Finset.mem_range,decide_eq_false_iff_not,
      Finset.mem_union,memb,a]
    omega
  have sep : Separated edge a b := by
    intro v hv w hw
    have vl : v<i-1 := Finset.mem_range.mp hv
    have wr := (memb w).mp hw
    exact ⟨by omega,by simp [edge,show v+1≠w by omega,show w+1≠v by omega],
      by simp [edge,show v+1≠w by omega,show w+1≠v by omega]⟩
  have shift : ∀ v w, edge (translate (i+2) v) (translate (i+2) w) = edge v w := by
    intro v w
    unfold edge translate
    change decide (i+2+v+1=i+2+w ∨ i+2+w+1=i+2+v) = decide (v+1=w ∨ w+1=v)
    congr 1
    apply propext
    omega
  rw [split,value_union _ _ _ sep]
  exact congrArg (score (i-1) ^^^ ·) (value_map edge edge (translate (i+2)) shift _)

theorem score_spec (n : Nat) :
    KaylesPair.IsMex (fun k => ∃ i<n, score (i-1) ^^^ score (n-i-2) = k) (score n) := by
  have eq (k : Nat) : (∃ i ∈ Finset.range n, value edge (drop edge (Finset.range n) i) = k) ↔
      (∃ i<n, score (i-1) ^^^ score (n-i-2) = k) := by
    constructor
    · rintro ⟨i,hi,hk⟩
      exact ⟨i,Finset.mem_range.mp hi,(option_value (Finset.mem_range.mp hi)).symm.trans hk⟩
    · rintro ⟨i,hi,hk⟩
      exact ⟨i,Finset.mem_range.mpr hi,(option_value hi).trans hk⟩
  have ht := value_spec edge (Finset.range n)
  exact ⟨fun hx => ht.1 ((eq _).mpr hx),fun k hk => (eq _).mp (ht.2 k hk)⟩

end KaylesRays.Path

#print axioms KaylesRays.Path.option_value
#print axioms KaylesRays.Path.score_spec

namespace KaylesRays.Path
open KaylesPair
def tab : List Nat := [0,1,1,2,0,3,1,1,0,3,3,2,2,4,0,5,2,2,3,3,0,1,1,3,0,2,1,1,0,4,5,2,7,4,0,1,1,2,0,3,1,1,0,3,3,2,2,4,4,5,5,2,3,3,0,1,1,3,0,2,1,1,0,4,5,3,7,4,8,1,1,2,0,3,1,1]
def expected (n : Nat) := tab[n]?.getD 0
def evalOptions (n : Nat) := (List.range n).map (fun i => expected (i-1) ^^^ expected (n-i-2))
def checked (n : Nat) :=
  let opts := evalOptions n
  let v := expected n
  decide (v ∉ opts) && (List.range v).all (fun u => decide (u∈opts))

set_option maxRecDepth 7500 in
set_option maxHeartbeats 2000000 in
private theorem verified : ∀ i : Fin 76, checked i.val = true := by
  decide +kernel

theorem score_eq_expected (n : Nat) (hn : n≤75) : score n = expected n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have h := verified ⟨n,by omega⟩
    simp only [checked, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    have ev (i : Nat) (hi : i<n) :
        score (i-1) ^^^ score (n-i-2) = expected (i-1) ^^^ expected (n-i-2) := by
      rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
    have eq (k : Nat) : k ∈ evalOptions n ↔ (∃ i<n, score (i-1) ^^^ score (n-i-2) = k) := by
      simp only [evalOptions,List.mem_map,List.mem_range]
      constructor
      · rintro ⟨i,hi,hk⟩
        exact ⟨i,hi,(ev i hi).trans hk⟩
      · rintro ⟨i,hi,hk⟩
        exact ⟨i,hi,(ev i hi).symm.trans hk⟩
    exact LiteralKayles.mex_unique (score_spec n)
      ⟨fun hx => h.1 ((eq _).mpr hx),fun k hk => (eq _).mp (h.2 _ hk)⟩

theorem options_seventy_five (k : Nat) :
    (∃ i<75, score (i-1) ^^^ score (75-i-2) = k) ↔ k ∈ [0,2,3,4,5,6,7,8] := by
  have e (i : Nat) (hi : i<75) : score (i-1) ^^^ score (75-i-2) =
      expected (i-1) ^^^ expected (75-i-2) := by
    rw [score_eq_expected _ (by omega),score_eq_expected _ (by omega)]
  change (∃ i<75, score (i-1) ^^^ score (75-i-2)=k) ↔ _
  have opts : (evalOptions 75).eraseDups = [3, 0, 8, 7, 6, 2, 5, 4] := by
    decide +kernel
  have values : k ∈ evalOptions 75 ↔ k ∈ [0,2,3,4,5,6,7,8] := by
    calc
      _ ↔ k ∈ (evalOptions 75).eraseDups := List.mem_eraseDups.symm
      _ ↔ _ := by
        rw [opts]
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        omega
  rw [←values,evalOptions,List.mem_map]
  simp only [List.mem_range]
  exact exists_congr (fun i => and_congr_right (fun hi => by rw [e i hi]))

#print axioms score_eq_expected
end KaylesRays.Path
#print axioms KaylesRays.Path.options_seventy_five

namespace KaylesRays.Modules
open LiteralKayles Sum

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/-- Edges in a disjoint union or complete join. -/
def between (join : Bool) (E : V → V → Bool) (D : W → W → Bool) :
    V ⊕ W → V ⊕ W → Bool
  | inl v, inl w => E v w
  | inr v, inr w => D v w
  | _, _ => join

def menu (E : V → V → Bool) (s : Finset V) : Finset Nat :=
  s.image (fun v => value E (drop E s v))

private theorem split_value (E : V → V → Bool) (D : W → W → Bool)
    (s : Finset V) (t : Finset W) :
    value (between false E D) (s.disjSum t) = value E s ^^^ value D t := by
  have eq : s.disjSum t = s.map Function.Embedding.inl ∪ t.map Function.Embedding.inr := by
    ext (v|w) <;> simp [Finset.mem_map]
  have sep : Separated (between false E D) (s.map Function.Embedding.inl)
      (t.map Function.Embedding.inr) := by
    rintro v hv w hw
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp hw
    simp [between]
  rw [eq,value_union _ _ _ sep,
    value_map E (between false E D) Function.Embedding.inl (fun _ _ => rfl),
    value_map D (between false E D) Function.Embedding.inr (fun _ _ => rfl)]

theorem move_left (join : Bool) (E : V → V → Bool) (D : W → W → Bool)
    (s : Finset V) (t : Finset W) (v : V) :
    value (between join E D) (drop (between join E D) (s.disjSum t) (inl v)) =
      value E (drop E s v) ^^^ (if join then 0 else value D t) := by
  cases join
  · have eq : drop (between false E D) (s.disjSum t) (inl v) =
        (drop E s v).disjSum t := by
      ext a
      change a ∈ Finset.filter _ (s.disjSum t) ↔ _
      rw [Finset.mem_filter]
      cases a <;> simp [drop,between]
    rw [eq,split_value]
    rfl
  · have eq : drop (between true E D) (s.disjSum t) (inl v) =
        (drop E s v).map Function.Embedding.inl := by
      ext a
      change a ∈ Finset.filter _ (s.disjSum t) ↔ _
      rw [Finset.mem_filter]
      cases a <;> simp [drop,between,Finset.mem_map]
    rw [eq,value_map E (between true E D) Function.Embedding.inl (fun _ _ => rfl)]
    simp

theorem move_right (join : Bool) (E : V → V → Bool) (D : W → W → Bool)
    (s : Finset V) (t : Finset W) (v : W) :
    value (between join E D) (drop (between join E D) (s.disjSum t) (inr v)) =
      value D (drop D t v) ^^^ (if join then 0 else value E s) := by
  cases join
  · have eq : drop (between false E D) (s.disjSum t) (inr v) =
        s.disjSum (drop D t v) := by
      ext a
      change a ∈ Finset.filter _ (s.disjSum t) ↔ _
      rw [Finset.mem_filter]
      cases a <;> simp [drop,between]
    rw [eq,split_value,Nat.xor_comm]
    rfl
  · have eq : drop (between true E D) (s.disjSum t) (inr v) =
        (drop D t v).map Function.Embedding.inr := by
      ext a
      change a ∈ Finset.filter _ (s.disjSum t) ↔ _
      rw [Finset.mem_filter]
      cases a <;> simp [drop,between,Finset.mem_map]
    rw [eq,value_map D (between true E D) Function.Embedding.inr (fun _ _ => rfl)]
    simp

/-- Exact option sets for modules. Disjoint union shifts by the value of the
other component, whereas complete join takes the union of their menus. -/
theorem combined (join : Bool) (E : V → V → Bool) (D : W → W → Bool)
    (s : Finset V) (t : Finset W) :
    menu (between join E D) (s.disjSum t) =
      ((menu E s).image fun k => k ^^^ (if join then 0 else value D t)) ∪
      ((menu D t).image fun k => k ^^^ (if join then 0 else value E s)) := by
  ext k
  simp only [menu,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro ⟨v,hv,hk⟩
    cases v with
    | inl u =>
      exact Or.inl ⟨_,⟨u,Finset.inl_mem_disjSum.mp hv,rfl⟩,(move_left join E D s t u).symm.trans hk⟩
    | inr u =>
      exact Or.inr ⟨_,⟨u,Finset.inr_mem_disjSum.mp hv,rfl⟩,(move_right join E D s t u).symm.trans hk⟩
  · rintro (⟨_,⟨v,hv,rfl⟩,eq⟩ | ⟨_,⟨v,hv,rfl⟩,eq⟩)
    · exact ⟨inl v,Finset.inl_mem_disjSum.mpr hv,(move_left join E D s t v).trans eq⟩
    · exact ⟨inr v,Finset.inr_mem_disjSum.mpr hv,(move_right join E D s t v).trans eq⟩

end KaylesRays.Modules

#print axioms KaylesRays.Modules.combined
