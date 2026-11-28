import RibbonsChecks

namespace ArmstrongRibbons

/-- Coordinatewise complement in the fundamental box. -/
private def reflectPoint (x : Point) : Point :=
  let ⟨a, b, c, d, e⟩ := x
  (⟨5 - a.val, by omega⟩, ⟨5 - b.val, by omega⟩, ⟨5 - c.val, by omega⟩,
    ⟨5 - d.val, by omega⟩, ⟨5 - e.val, by omega⟩)

private theorem reflect_twice (x : Point) : reflectPoint (reflectPoint x) = x := by
  rcases x with ⟨a, b, c, d, e⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  simp only [reflectPoint, Prod.mk.injEq, Fin.ext_iff]
  omega

private theorem reflect_mem {lo hi : ℤ} (x : Point) :
    reflectPoint x ∈ Slice (25 - hi) (25 - lo) ↔ x ∈ Slice lo hi := by
  change (25 - hi ≤ (total (reflectPoint x) : ℤ) ∧ (total (reflectPoint x) : ℤ) ≤ 25 - lo) ↔
    (lo ≤ (total x : ℤ) ∧ (total x : ℤ) ≤ hi)
  rcases x with ⟨a, b, c, d, e⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  simp only [reflectPoint, total, suffix]
  omega

private theorem reflect_step {x y : Point} (h : step x y) :
    step (reflectPoint y) (reflectPoint x) := by
  rcases x with ⟨a, b, c, d, e⟩
  rcases y with ⟨f, g, i, j, k⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  have hf := f.isLt
  have hg := g.isLt
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  simp only [step, reflectPoint, suffixLE, suffix, height] at *
  omega

private theorem reflect_partition {lo hi : ℤ} (h : RibbonPartition (Slice lo hi)) :
    RibbonPartition (Slice (25 - hi) (25 - lo)) := by
  obtain ⟨ribbons, hdup, hdom, hrows⟩ := h
  let lifted := (ribbons.map List.reverse).reverse.map (List.map reflectPoint)
  have hflat : lifted.flatten = ribbons.flatten.reverse.map reflectPoint := by
    change (((ribbons.map List.reverse).reverse).map (List.map reflectPoint)).flatten = _
    rw [← List.map_flatten, ← List.reverse_flatten]
  have hmem : ∀ x, x ∈ lifted.flatten ↔ x ∈ Slice (25 - hi) (25 - lo) := by
    intro x
    rw [hflat, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (reflect_mem p).mpr ((hdom p).mp (List.mem_reverse.mp hp))
    · intro hx
      have hp : reflectPoint (reflectPoint x) ∈ Slice (25 - hi) (25 - lo) := by
        rw [reflect_twice]
        exact hx
      exact ⟨reflectPoint x, List.mem_reverse.mpr ((hdom _).mpr ((reflect_mem _).mp hp)),
        reflect_twice x⟩
  refine ⟨lifted, ?_, hmem, ?_⟩
  · rw [hflat]
    exact (List.nodup_reverse.mpr hdup).map (fun _ _ he => by
      simpa only [reflect_twice] using congrArg reflectPoint he)
  · intro row hrow
    obtain ⟨reversed, hreversed, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hreversed)
    obtain ⟨hlen, hchain⟩ := hrows original horiginal
    have hr : (original.reverse.map reflectPoint).IsChain step :=
      (List.isChain_map _).mpr (List.isChain_reverse.mpr (hchain.imp fun _ _ hs =>
        reflect_step ⟨hs.1.2.2.2.1, hs.2⟩))
    refine ⟨by simpa using hlen, hr.imp_of_mem_imp ?_⟩
    intro x y hx hy hs
    exact ⟨cover_of_step ((hmem x).mp (List.mem_flatten_of_mem hrow hx))
      ((hmem y).mp (List.mem_flatten_of_mem hrow hy)) hs, hs.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem all_slices :
    RibbonPartition (Slice 0 1) ∧ RibbonPartition (Slice 2 5) ∧
    RibbonPartition (Slice 6 7) ∧ RibbonPartition (Slice 8 11) ∧
    RibbonPartition (Slice 12 13) ∧ RibbonPartition (Slice 14 17) ∧
    RibbonPartition (Slice 18 19) ∧ RibbonPartition (Slice 20 23) ∧
    RibbonPartition (Slice 24 25) := by
  have s₁ := checked0_1
  have s₂ := checked2_5
  have s₃ := checked6_7
  have s₄ := checked8_11
  have s₅ := checked12_13
  exact ⟨s₁, s₂, s₃, s₄, s₅, reflect_partition s₄, reflect_partition s₃,
    reflect_partition s₂, reflect_partition s₁⟩

private theorem coprime_residue (z : ℤ) : z.gcd 6 = 1 ↔ z % 6 = 1 ∨ z % 6 = 5 := by
  rw [← Int.gcd_emod]
  have h : z % 6 = 0 ∨ z % 6 = 1 ∨ z % 6 = 2 ∨ z % 6 = 3 ∨ z % 6 = 4 ∨ z % 6 = 5 := by
    omega
  rcases h with h | h | h | h | h | h <;> rw [h] <;> decide

private def cutoffs : List ℤ := [1, 5, 7, 11, 13, 17, 19, 23, 25]

private theorem mem_cutoffs (c : ℤ) (hlo : 1 ≤ c) (hhi : c ≤ 25) (hc : c.gcd 6 = 1) :
    c ∈ cutoffs := by
  have finite : ∀ k : Fin 26, 1 ≤ (k.val : ℤ) → (k.val : ℤ).gcd 6 = 1 →
      (k.val : ℤ) ∈ cutoffs := by decide +kernel
  let k : Fin 26 := ⟨c.toNat, by omega⟩
  have heq : (k.val : ℤ) = c := Int.toNat_of_nonneg (by omega)
  rw [← heq] at hlo hc ⊢
  exact finite k hlo hc

private theorem cutoff_predecessor (c prior : ℤ) (hc : c.gcd 6 = 1)
    (hpc : prior < c) (hp : prior.gcd 6 = 1)
    (hmax : ∀ d : ℤ, d < c → d.gcd 6 = 1 → d ≤ prior) :
    prior = if c % 6 = 1 then c - 2 else c - 4 := by
  have hpmod := (coprime_residue prior).mp hp
  rcases (coprime_residue c).mp hc with h | h
  · rw [ite_eq_left h]
    have hlower : c - 2 ≤ prior :=
      hmax (c - 2) (by omega) ((coprime_residue _).mpr (Or.inr (by omega)))
    omega
  · rw [ite_eq_right (by omega)]
    have hlower : c - 4 ≤ prior :=
      hmax (c - 4) (by omega) ((coprime_residue _).mpr (Or.inl (by omega)))
    omega

/-- Conjecture 10.2 with `a = 6`, for every cutoff and its greatest coprime predecessor. -/
theorem conjecture_10_2_a6 (c prior : ℤ)
    (hc₁ : 1 ≤ c) (hc₂ : c ≤ (6 - 1) ^ 2) (hc : c.gcd 6 = 1)
    (hpc : prior < c) (hp : prior.gcd 6 = 1)
    (hmax : ∀ d : ℤ, d < c → d.gcd 6 = 1 → d ≤ prior) :
    RibbonPartition {x | prior < (total x : ℤ) ∧ (total x : ℤ) ≤ c} := by
  have heq : {x : Point | prior < (total x : ℤ) ∧ (total x : ℤ) ≤ c} = Slice (prior + 1) c := by
    ext x
    change (prior < (total x : ℤ) ∧ (total x : ℤ) ≤ c) ↔
      (prior + 1 ≤ (total x : ℤ) ∧ (total x : ℤ) ≤ c)
    omega
  rw [heq]
  rcases all_slices with ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉⟩
  have hprior := cutoff_predecessor c prior hc hpc hp hmax
  have hc_values := mem_cutoffs c hc₁ hc₂ hc
  rw [hprior]
  simp only [cutoffs, List.mem_cons, List.not_mem_nil, or_false] at hc_values
  rcases hc_values with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s₁
  · exact s₂
  · exact s₃
  · exact s₄
  · exact s₅
  · exact s₆
  · exact s₇
  · exact s₈
  · exact s₉

#print axioms conjecture_10_2_a6

end ArmstrongRibbons
