module

public import Mathlib.Combinatorics.Hall.Finite
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


@[simp] theorem mem_nbr {x y : V n} : y ∈ G.nbr x ↔ G.adj x y := by classical simp [nbr]

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

theorem count_edges (c : V n → Bool) (v : V n) :
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

namespace Graffiti392.Graph
open Finset Classical
noncomputable section
variable {n : Nat} (G : Graph n)

/-- Every nonempty subset of the unpaid chain interiors has a vertex with
at most one neighbor in the subset. Connectedness rules out a cycle component. -/
theorem peel (hc : G.Connected) {S : Finset (V n)} (hs : S ⊆ G.inside)
    (hne : S.Nonempty) : ∃ v ∈ S, (G.nbr v ∩ S).card ≤ 1 := by
  obtain ⟨u,hu⟩ := G.minimum_nonempty (let ⟨x,_⟩ := hne; ⟨x⟩)
  have out : u ∉ S := fun h => (G.mem_inside.mp (hs h)).2.2 (G.mem_paid.mpr (.inl hu))
  obtain ⟨v,hv,w,hw,hadj⟩ := hc S hne ⟨u,out⟩
  have strict : (G.nbr v ∩ S).card < (G.nbr v).card := by
    apply card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left,fun eq => hw
      (mem_inter.mp (eq ▸ G.mem_nbr.mpr hadj)).2⟩
  have d := (G.mem_inside.mp (hs hv)).1
  change (G.nbr v).card = 2 at d
  exact ⟨v,hv,by omega⟩

theorem color_subset (hc : G.Connected) (S : Finset (V n)) (hs : S ⊆ G.inside) :
    ∃ c : V n → Bool, ∀ x ∈ S, ∀ y ∈ S, G.adj x y → c x ≠ c y := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨v,hv,small⟩ := G.peel hc hs hne
    obtain ⟨c,valid⟩ := color_subset hc (S.erase v) ((erase_subset ..).trans hs)
    let b := if h : (G.nbr v ∩ S).Nonempty then !(c h.choose) else false
    let f (x : V n) := if x = v then b else c x
    have incident {y : V n} (hy : y ∈ S) (a : G.adj v y) : f v ≠ f y := by
      have ny : y ≠ v := fun e => G.loopless v (e ▸ a)
      have yy : y ∈ G.nbr v ∩ S := mem_inter.mpr ⟨G.mem_nbr.mpr a,hy⟩
      have h : (G.nbr v ∩ S).Nonempty := ⟨y,yy⟩
      have e := (card_le_one.mp small) _ h.choose_spec y yy
      simp [f,b,h,ny,e]
    refine ⟨f,?_⟩
    intro x hx y hy a
    by_cases ex : x = v
    · subst x; exact incident hy a
    by_cases ey : y = v
    · subst y; exact Ne.symm (incident hx (G.symm a))
    simpa [f,ex,ey] using valid x (mem_erase.mpr ⟨ex,hx⟩) y (mem_erase.mpr ⟨ey,hy⟩) a
  · exact ⟨fun _ => false,fun _ hx => (hne ⟨_,hx⟩).elim⟩
termination_by S.card
decreasing_by exact card_erase_lt_of_mem hv

def useful (c : V n → Bool) (x : V n) :=
  (G.nbr x).filter (fun y => y ∈ G.paid ∨ c x ≠ c y)

theorem degree_pos (hn : 2 < n) (hc : G.Connected) (v : V n) : 0 < G.degree v := by
  have other : ∃ w : V n, w ∉ ({v} : Finset _) := by
    by_contra! bad
    have sub : (univ : Finset (V n)) ⊆ {v} := fun w _ => bad w
    have h := card_le_card sub
    simp at h
    omega
  obtain ⟨x,hx,y,_,a⟩ := hc {v} (singleton_nonempty _) other
  obtain rfl := mem_singleton.mp hx
  exact card_pos.mpr ⟨y,G.mem_nbr.mpr a⟩

theorem adequate_cut (hn : 2 < n) (hc : G.Connected) :
    ∃ c : V n → Bool, ∀ x ∉ G.paid, 2 ≤ (G.useful c x).card := by
  classical
  obtain ⟨b,hb⟩ := G.color_subset hc G.inside (fun _ h => h)
  let seed (x : V n) := if x ∈ G.inside then b x else decide (G.degree x = 2)
  obtain ⟨c,hcfix,free⟩ := G.extend_cut G.fixed seed
  refine ⟨c,?_⟩
  intro x hx
  have notOne {w : V n} (h : w ∉ G.paid) : (G.twoNbr w).card ≠ 1 :=
    fun e => h (G.mem_paid.mpr (.inr (G.mem_exceptional.mpr e)))
  have atMost (w : V n) : (G.twoNbr w).card ≤ G.degree w := card_le_card (G.twoNbr_sub w)
  have cHigh {v w : V n} (a : G.adj v w) (dv : G.degree v ≠ 2) (dw : G.degree w = 2) :
      c v = false := by
    have p : 0 < (G.twoNbr v).card := card_pos.mpr ⟨w,G.mem_twoNbr.mpr ⟨a,dw⟩⟩
    have f := hcfix v (.inr p)
    have o : v ∉ G.inside := fun h => dv (G.mem_inside.mp h).1
    simpa [seed,o,dv] using f
  have cIsolated {v : V n} (dv : G.degree v = 2) (z : (G.twoNbr v).card = 0) :
      c v = true := by
    have o : v ∉ G.inside := fun h => by have := (G.mem_inside.mp h).2.1; omega
    simpa only [seed,ite_eq_right o,decide_eq_true dv] using hcfix v (.inl dv)
  by_cases dx : G.degree x = 2
  · suffices sub : G.nbr x ⊆ G.useful c x by
      have h := card_le_card sub
      change (G.nbr x).card = 2 at dx
      omega
    intro y hy
    apply mem_filter.mpr
    refine ⟨hy,?_⟩
    by_cases paid : y ∈ G.paid
    · exact .inl paid
    apply Or.inr
    have a := G.mem_nbr.mp hy
    by_cases q : (G.twoNbr x).card = 0
    · have dy : G.degree y ≠ 2 := fun h => by
        have t := card_pos.mpr (show (G.twoNbr x).Nonempty from ⟨y,G.mem_twoNbr.mpr ⟨a,h⟩⟩)
        omega
      rw [cIsolated dx q,cHigh (G.symm a) dy dx]
      decide
    · have t := atMost x
      have o := notOne hx
      have tx : (G.twoNbr x).card = 2 := by omega
      have ix := G.mem_inside.mpr ⟨dx,tx,hx⟩
      have dy := (G.mem_twoNbr.mp ((G.all_neighbors_two dx tx).symm ▸ hy)).2
      have ypos := card_pos.mpr (show (G.twoNbr y).Nonempty from ⟨x,G.mem_twoNbr.mpr ⟨G.symm a,dx⟩⟩)
      have ty := atMost y
      have oy := notOne paid
      have iy := G.mem_inside.mpr ⟨dy,by omega,paid⟩
      have cx := hcfix x (.inl dx)
      have cy := hcfix y (.inl dy)
      rw [cx,cy]
      simpa only [seed,ite_eq_left ix,ite_eq_left iy] using hb x ix y iy a
  · by_cases q : 0 < (G.twoNbr x).card
    · have sub : G.twoNbr x ⊆ G.useful c x := by
        intro y hy
        obtain ⟨a,dy⟩ := G.mem_twoNbr.mp hy
        refine mem_filter.mpr ⟨G.mem_nbr.mpr a,?_⟩
        by_cases paid : y ∈ G.paid
        · exact .inl paid
        have noTwo : (G.twoNbr y).card ≠ 2 := fun h => dx
          (G.mem_twoNbr.mp ((G.all_neighbors_two dy h).symm ▸ G.mem_nbr.mpr (G.symm a))).2
        have oy := notOne paid
        have ty := atMost y
        have z : (G.twoNbr y).card = 0 := by omega
        exact .inr (by rw [cHigh a dx dy,cIsolated dy z]; decide)
      have t := card_le_card sub
      have o := notOne hx
      omega
    · have bal := free x (fun h => h.elim dx q)
      have tot := G.degree_split c x
      have dm : 2 < G.degree x := by
        have pd := G.degree_pos hn hc x
        by_contra! low
        exact hx (G.mem_paid.mpr (.inl (G.mem_minimum.mpr (fun y => by
          have := G.degree_pos hn hc y
          omega))))
      have sub : G.opp c x ⊆ G.useful c x := by
        intro y hy
        obtain ⟨ha,ho⟩ := mem_filter.mp hy
        exact mem_filter.mpr ⟨ha,.inr ho⟩
      have h := card_le_card sub
      omega

end
end Graffiti392.Graph

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

namespace Graffiti392.Graph
open Finset Classical
noncomputable section
variable {n : Nat} (G : Graph n)

/-- Graffiti.pc 392b, announced in January 2010. -/
theorem conjecture392b (hn : 2 < n) (hc : G.Connected) :
    G.gammaTwo ≤ G.matching (univ \ G.minimum) + G.minimum.card + G.exceptional.card := by
  classical
  obtain ⟨c,good⟩ := G.adequate_cut hn hc
  let U := univ \ G.paid
  obtain ⟨s,matching,cover⟩ := G.crossing_cover U c
  have rem {x : V n} (h : x ∉ G.paid) : x ∈ U := mem_sdiff.mpr ⟨mem_univ _,h⟩
  have dom : G.TwoDominates (s ∪ G.paid) := by
    intro x hx
    have xs : x ∉ s := fun h => hx (mem_union_left _ h)
    have xp : x ∉ G.paid := fun h => hx (mem_union_right _ h)
    apply (good x xp).trans (card_le_card ?_)
    intro y hy
    obtain ⟨ha,choice⟩ := mem_filter.mp hy
    refine mem_inter.mpr ⟨ha,?_⟩
    by_cases yp : y ∈ G.paid
    · exact mem_union_right _ yp
    have edge : G.cross U c x y :=
      ⟨rem xp,rem yp,G.mem_nbr.mp ha,choice.resolve_left yp⟩
    exact mem_union_left _ ((cover x y edge).resolve_left xs)
  have bigger : U ⊆ univ \ G.minimum := by
    intro x hx
    exact mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_sdiff.mp hx).2 (G.mem_paid.mpr (.inl h))⟩
  obtain ⟨ss,f,inj,hf⟩ := matching
  have m := G.le_matching (show G.Matches (univ \ G.minimum) s from
    ⟨ss.trans bigger,f,inj,fun i => ⟨bigger (hf i).1,(hf i).2⟩⟩)
  have d := G.gammaTwo_le dom
  have bound := card_union_le s G.paid
  have p : G.paid.card ≤ G.minimum.card + G.exceptional.card := card_union_le ..
  omega

end
end Graffiti392.Graph
