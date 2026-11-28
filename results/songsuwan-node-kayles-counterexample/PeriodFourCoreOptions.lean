import RayCounts
import PeriodFourLiteral
import PeriodFourMenus

namespace KaylesRays.PeriodFourRealization
open LiteralKayles Sum MixedPaths PeriodFourLiteral PeriodFourMenus

/-- The root play, the neighboring core plays, and the seven mark plays. -/
def CoreOptions (f : Nat → Nat → Nat → Bool → Nat) (h : Fin 8)
    (x c : Nat) (z : Bool) (d k : Nat) : Prop :=
  ((if h.val=0 then 1 else 0) ^^^ (c%2) = k) ∨
  (∃ a∈menu h, a ^^^ d=k) ∨
  (h.val=0 ∧ ∃ i : Fin 7, f (i.val+1) x c z=k)

theorem core_options (f : Nat → Nat → Nat → Bool → Nat) (h : Fin 8)
    (ids : Finset Nat) (kind : Nat → Nat) (ok : liveKinds ids kind)
    (quiet : h.val=0 → ∀ i : Fin 7,
      MixedPaths.score coreAdj none (hostBoard ⟨i.val+1,by omega⟩) ids (arms kind) =
        f (i.val+1) (count ids kind 5) (count ids kind 3) (odd (count ids kind 1))) (k : Nat) :
    (∃ v∈hostBoard h, after coreAdj none (hostBoard h) ids (arms kind) (inl v)=k) ↔
      CoreOptions f h (count ids kind 5) (count ids kind 3)
        (odd (count ids kind 1)) (detachedXor ids kind) k := by
  let play := fun v => after coreAdj none (hostBoard h) ids (arms kind) (inl v)
  have hub : play none = (if h.val=0 then 1 else 0) ^^^ (count ids kind 3 % 2) := by
    unfold play after
    rw [host_drop,hostBoard_hub]
    change MixedPaths.score coreAdj none ((farBoard h).image some) ids (fun n => (arms kind n).erase 0) = _
    rw [detached_trim coreAdj none _ ids kind ok (by simp),core_image_value,hub_value]
  have near (v : Fin 279) (hv : v∈nearBoard h) :
      play (some v) = value coreEdge (drop coreEdge (coreBoard h) v) ^^^ detachedXor ids kind := by
    unfold play after
    rw [host_drop,hostBoard_near h hv]
    change MixedPaths.score coreAdj none ((drop coreEdge (coreBoard h) v).image some)
      ids (arms kind) = _
    rw [detached_full coreAdj none _ ids kind ok (by simp),core_image_value]
  have far (hz : h.val=0) (i : Fin 7) :
      play (some (marks i)) = f (i.val+1) (count ids kind 5) (count ids kind 3) (odd (count ids kind 1)) := by
    have e : h=0 := Fin.ext hz
    unfold play after
    rw [e,host_drop,hostBoard_quiet]
    exact quiet hz i
  have noFar (v : Fin 279) (hv : v ∈ coreBoard h) (hm : v ∈ marked) : h.val=0 := by
    have hf : v ∈ farBoard h := Finset.mem_inter.mpr ⟨hv,hm⟩
    by_contra n
    simp [far_eq h,n] at hf
  unfold CoreOptions
  change (∃ v∈hostBoard h, play v=k) ↔ _
  constructor
  · rintro ⟨v,hv,q⟩
    cases v with
    | none => exact Or.inl (hub.symm.trans q)
    | some v =>
      have hv' := (hostBoard_some_mem h v).mp hv
      by_cases hm : v∈marked
      · have hz := noFar v hv' hm
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
        exact Or.inr (Or.inr ⟨hz,i,(far hz i).symm.trans q⟩)
      · have hv'' : v∈nearBoard h := Finset.mem_sdiff.mpr ⟨hv',hm⟩
        refine Or.inr (Or.inl ⟨_,?_,(near v hv'').symm.trans q⟩)
        rw [← near_menu]
        exact Finset.mem_image.mpr ⟨v,hv'',rfl⟩
  · rintro (q|⟨a,ha,q⟩|⟨hz,i,q⟩)
    · exact ⟨none,hostBoard_none_mem h,hub.trans q⟩
    · rw [← near_menu] at ha
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
      exact ⟨some v,(hostBoard_some_mem h v).mpr (Finset.mem_sdiff.mp hv).1,(near v hv).trans q⟩
    · have e : h=0 := Fin.ext hz
      exact ⟨some (marks i),(hostBoard_some_mem h _).mpr (by rw [e]; simp [coreBoard]),(far hz i).trans q⟩

end KaylesRays.PeriodFourRealization
