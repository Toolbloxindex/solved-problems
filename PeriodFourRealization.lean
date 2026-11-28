module

public import PeriodFourCoreOptions
public import RayCounts
public import PeriodFourTable
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace KaylesRays.PeriodFourRealization
open LiteralKayles Sum MixedPaths PeriodFourLiteral PeriodFourMenus

private theorem mask_eq (h : Fin 8) : mask h = PeriodFour.masks[h.val]?.getD 0 := rfl
private theorem erased_eq (h : Fin 8) : erased h = PeriodFour.erased[h.val]?.getD 0 := rfl

private theorem contribution_eq (v n : Nat) : contribution v n = v*(n%2) := by
  by_cases h : n%2=1
  · simp [contribution,odd,h]
  · have h0 : n%2=0 := by omega
    simp [contribution,odd,h0]

private def detachedBits (x c : Nat) (z : Bool) :=
  (3*(x%2)) ^^^ (2*(c%2)) ^^^ z.toNat

set_option maxHeartbeats 800000 in
private theorem options_eq (f : Nat → Int → Int → Bool → Nat) (h : Fin 8)
    (x c : Nat) (z : Bool) (k : Nat) :
    k ∈ Positive.options (PeriodFour.exits f h.val) (f h.val) x c z ↔
      CoreOptions (fun h x c => f h x c) h x c z (detachedBits x c z) k ∨
      RayOptions (fun x c => f h.val x c) x c z (erased h ^^^ detachedBits x c z) k := by
  unfold detachedBits
  have px : ((x : Int)%2).toNat = x%2 := by omega
  have pc : ((c : Int)%2).toNat = c%2 := by omega
  have xp : 0<(x:Int) ↔ 0<x := by omega
  have cp : 0<(c:Int) ↔ 0<c := by omega
  have quietExists :
      (∃ i : Nat, i<7 ∧ k=f (i+1) x c z) ↔ ∃ i : Fin 7, k=f (i.val+1) x c z := by
    constructor
    · rintro ⟨i,hi,he⟩
      exact ⟨⟨i,hi⟩,he⟩
    · rintro ⟨i,hi⟩
      exact ⟨i.val,i.isLt,hi⟩
  have leftSub (hx : 0<x) : (x:Int)-1 = ((x-1:Nat):Int) := by omega
  have rightSub (hc : 0<c) : (c:Int)-1 = ((c-1:Nat):Int) := by omega
  have rightAdd : (c:Int)+1 = ((c+1:Nat):Int) := by omega
  have hubEq : (c%2) ^^^ (if h.val=0 then 1 else 0) =
      (if h.val=0 then 1 else 0) ^^^ (c%2) := Nat.xor_comm ..
  unfold Positive.options PeriodFour.exits CoreOptions RayOptions
  simp only [px,pc,xp,cp,←mask_eq,←erased_eq,rightAdd,hubEq,List.mem_append,List.mem_map]
  have expr (d : Nat) (k : Nat) :
      (∃ a∈(List.range 12).filter (fun k => (mask h).testBit k), a ^^^ d=k) ↔
      ∃ a∈menu h, a ^^^ d=k := by simp [menu]
  simp only [expr]
  by_cases hx : 0<x <;> by_cases hc : 0<c <;> by_cases hz : h.val=0 <;>
    simp [hx,hc,hz,leftSub,rightSub,eq_comm]
  all_goals try rw [quietExists]
  all_goals simp only [or_assoc,or_left_comm,or_comm]

/-- The literal mex equation at one mixed board, once the values of
its smaller hub-preserving successors are known. -/
theorem board_mex (f : Nat → Int → Int → Bool → Nat) (h : Fin 8)
    (ids : Finset Nat) (kind : Nat → Nat) (ok : liveKinds ids kind) (leaves : 0<count ids kind 1)
    (quiet : h.val=0 → ∀ i : Fin 7,
      MixedPaths.score coreAdj none (hostBoard ⟨i.val+1,by omega⟩) ids (arms kind) =
        f (i.val+1) (count ids kind 5) (count ids kind 3) (odd (count ids kind 1)))
    (lower : ∀ js types, liveKinds js types → 0<count js types 1 →
      2*count js types 5+count js types 3 < 2*count ids kind 5+count ids kind 3 →
      MixedPaths.score coreAdj none (hostBoard h) js (arms types) =
        f h.val (count js types 5) (count js types 3) (odd (count js types 1))) :
    let x := count ids kind 5
    let c := count ids kind 3
    let z := odd (count ids kind 1)
    Quartet.Mex (· ∈ Positive.options (PeriodFour.exits f h.val) (f h.val) x c z)
      (MixedPaths.score coreAdj none (hostBoard h) ids (arms kind)) := by
  have g (k : Nat) :
      k ∈ Positive.options (PeriodFour.exits f h.val) (f h.val)
        (count ids kind 5) (count ids kind 3) (odd (count ids kind 1)) ↔
      ∃ a ∈ mixed (hostBoard h) ids (arms kind), after coreAdj none (hostBoard h) ids (arms kind) a=k := by
    rw [options_eq]
    have d : detachedXor ids kind =
        detachedBits (count ids kind 5) (count ids kind 3) (odd (count ids kind 1)) := by
      simp only [detachedXor,detachedBits,contribution_eq]
    have e : value coreAdj ((hostBoard h).erase none) = erased h := by
      rw [hostBoard_erase,core_image_value,erased_value]
    have a := core_options (fun h x c => f h x c) h ids kind ok quiet k
    have b := ray_options coreAdj none (hostBoard h) (hostBoard_none_mem h) ids kind ok
      (fun x c => f h.val x c) leaves lower k
    rw [d] at a b
    rw [e] at b
    rw [← a,← b]
    constructor
    · rintro (⟨v,hv,hk⟩|⟨n,hn,i,hi,hk⟩)
      · exact ⟨inl v, (mem_old ..).mpr hv,hk⟩
      · exact ⟨inr (n,i), (mem_ray ..).mpr ⟨hn,hi⟩,hk⟩
    · rintro ⟨v,hv,hk⟩
      rcases v with (v|⟨n,i⟩)
      · exact Or.inl ⟨v,(mem_old ..).mp hv,hk⟩
      · exact Or.inr ⟨n,(mem_ray .. |>.mp hv).1,i,(mem_ray .. |>.mp hv).2,hk⟩
  have sp := value_spec (siteEdge coreAdj none) (mixed (hostBoard h) ids (arms kind))
  exact ⟨fun hm => sp.1 ((g _).mp hm),fun k hk => (g k).mpr (sp.2 k hk)⟩

private def rank (h : Fin 8) (ids : Finset Nat) (kind : Nat → Nat) :=
  2*(2*count ids kind 5+count ids kind 3) + if h.val=0 then 1 else 0

/-- Independently of the order of physical labels, every positive-leaf
inventory realizes the corresponding row of the finite table. -/
theorem mixed_eq_profile (h : Fin 8) (ids : Finset Nat) (kind : Nat → Nat)
    (ok : liveKinds ids kind) (leaves : 0<count ids kind 1) :
    MixedPaths.score coreAdj none (hostBoard h) ids (arms kind) =
      PeriodFour.profile h.val (count ids kind 5) (count ids kind 3) (odd (count ids kind 1)) := by
  let R := rank h ids kind
  suffices all : ∀ n, ∀ h ids kind, rank h ids kind=n →
      liveKinds ids kind → 0<count ids kind 1 →
      MixedPaths.score coreAdj none (hostBoard h) ids (arms kind) =
        PeriodFour.profile h.val (count ids kind 5) (count ids kind 3) (odd (count ids kind 1)) by
    exact all R h ids kind rfl ok leaves
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro h ids kind hr ok leaves
    refine Positive.unique (board_mex PeriodFour.profile h ids kind ok leaves ?_ ?_)
      (PeriodFour.profile_mex h.val h.isLt _ _ _ (by omega) (by omega))
    · intro hh i
      apply ih (rank ⟨i.val+1,by omega⟩ ids kind) _ _ _ _ rfl ok leaves
      rw [←hr]
      simp [rank,hh]
    · intro js types good live smaller
      apply ih (rank h js types) _ h js types rfl good live
      rw [←hr]
      unfold rank
      omega

private def leafCount (z : Bool) : Nat := if z then 1 else 2
private def idsFor (x c : Nat) (z : Bool) : Finset Nat := Finset.range (leafCount z+c+x)
private def kindFor (c : Nat) (z : Bool) (n : Nat) : Nat :=
  if n<leafCount z then 1 else if n<leafCount z+c then 3 else 5

private theorem canonicalCounts (x c : Nat) (z : Bool) :
    count (idsFor x c z) (kindFor c z) 5=x ∧ count (idsFor x c z) (kindFor c z) 3=c ∧
    count (idsFor x c z) (kindFor c z) 1=leafCount z := by
  have f (m : Nat) : kindFor c z m=5 ↔ leafCount z+c≤m := by
    unfold kindFor
    split_ifs <;> omega
  have t (m : Nat) : kindFor c z m=3 ↔ leafCount z≤m ∧ m<leafCount z+c := by
    unfold kindFor
    split_ifs <;> omega
  have l (m : Nat) : kindFor c z m=1 ↔ m<leafCount z := by
    unfold kindFor
    split_ifs <;> omega
  have a : (idsFor x c z).filter (fun m => kindFor c z m=5) = Finset.Ico (leafCount z+c) (leafCount z+c+x) := by
    ext m
    rw [Finset.mem_filter,Finset.mem_Ico,idsFor,Finset.mem_range,f]
    tauto
  have b : (idsFor x c z).filter (fun m => kindFor c z m=3) = Finset.Ico (leafCount z) (leafCount z+c) := by
    ext m
    rw [Finset.mem_filter,Finset.mem_Ico,idsFor,Finset.mem_range,t]
    omega
  have d : (idsFor x c z).filter (fun m => kindFor c z m=1) = Finset.range (leafCount z) := by
    ext m
    rw [Finset.mem_filter,idsFor,Finset.mem_range,Finset.mem_range,l]
    omega
  simp [count,a,b,d]

private theorem canonicalKinds (x c : Nat) (z : Bool) : liveKinds (idsFor x c z) (kindFor c z) := by
  intro n _
  unfold kindFor
  split_ifs <;> simp

/-- Each of the eight rows is evaluated on its own physical core board. -/
def literalProfile (h : Nat) (x c : Int) (z : Bool) : Nat :=
  if hh : h<8 then
    MixedPaths.score coreAdj none (hostBoard ⟨h,hh⟩) (idsFor x.toNat c.toNat z) (arms (kindFor c.toNat z))
  else 0

theorem literal_eq_profile (h : Nat) (hh : h<8) (x c : Int) (z : Bool) (hx : 0≤x) (hc : 0≤c) :
    literalProfile h x c z = PeriodFour.profile h x c z := by
  obtain ⟨a,b,d⟩ := canonicalCounts x.toNat c.toNat z
  have one : 0<leafCount z := by cases z <;> decide
  have parity : odd (leafCount z)=z := by cases z <;> decide
  rw [literalProfile,dite_eq_left hh,mixed_eq_profile _ _ _ (canonicalKinds x.toNat c.toNat z) (d.symm ▸ one),
    a,b,d,parity,Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hc]

/-- The exact eight-board hypothesis of witness_recurrence, with the
function realized by literal closed-neighborhood Grundy values. -/
theorem literal_rule :
    ∀ h<8, ∀ x c z, 0≤x → 0≤c →
      Quartet.Mex (· ∈ Positive.options (PeriodFour.exits literalProfile h) (literalProfile h) x c z)
        (literalProfile h x c z) := by
  intro h hh x c z hx hc
  obtain ⟨a,b,d⟩ := canonicalCounts x.toNat c.toNat z
  have one : 0<leafCount z := by cases z <;> decide
  have parity : odd (leafCount z)=z := by cases z <;> decide
  have runs := board_mex literalProfile ⟨h,hh⟩ (idsFor x.toNat c.toNat z) (kindFor c.toNat z)
    (canonicalKinds x.toNat c.toNat z) (d.symm ▸ one) (by
      intro _ i
      rw [mixed_eq_profile _ _ _ (canonicalKinds x.toNat c.toNat z) (d.symm ▸ one)]
      exact (literal_eq_profile (i.val+1) (by omega) _ _ _ (by omega) (by omega)).symm)
    (by
      intro js types good live _
      rw [mixed_eq_profile _ _ _ good live]
      exact (literal_eq_profile h hh _ _ _ (by omega) (by omega)).symm)
  dsimp only at runs
  simp only [a,b,d,parity,Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hc] at runs
  have rhs : literalProfile h x c z =
      MixedPaths.score coreAdj none (hostBoard ⟨h,hh⟩)
        (idsFor x.toNat c.toNat z) (arms (kindFor c.toNat z)) := by
    simp only [literalProfile,dite_eq_left hh]
  rw [rhs]
  exact runs

end KaylesRays.PeriodFourRealization
