import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring

namespace JacobiProjective

open Polynomial

/-- The first-order operator after the substitution x = y/(1+y). -/
noncomputable def step (a b : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * (1+X) * p.derivative + (C a + C b * X) * p

theorem step_at_negOne (a b : ℝ) (p : ℝ[X]) :
    (step a b p).eval (-1) = (a-b)*p.eval (-1) := by
  simp [step, sub_eq_add_neg]

theorem step_at_zero (a b : ℝ) (p : ℝ[X]) :
    (step a b p).eval 0 = a*p.eval 0 := by
  simp [step]

theorem step_at_root {a b r : ℝ} {p : ℝ[X]} (hr : p.eval r = 0) :
    (step a b p).eval r = r*(1+r)*p.derivative.eval r := by
  simp [step, hr]

private theorem step_pole_once (a b : ℝ) (p : ℝ[X]) :
    step a b ((1+X)*p) = (1+X)*step a (b+1) p := by
  simp [step, derivative_mul, map_add]
  ring

/-- Extract a boundary root at y = -1 with any multiplicity before counting the open gaps. -/
theorem step_pole (a b : ℝ) (m : ℕ) (p : ℝ[X]) :
    step a b ((1+X)^m*p) = (1+X)^m*step a (b+m) p := by
  induction m generalizing b with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, step_pole_once, ih]
    simp only [Nat.cast_succ]
    rw [show b+1+(m : ℝ) = b+((m : ℝ)+1) by ring]
    ring

private theorem exists_root_between {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) :
    ∃ r ∈ Set.Ioo a b, p.eval r = 0 := by
  have hin : (0 : ℝ) ∈ p.eval '' Set.Icc a b := by
    rcases le_or_gt (p.eval a) 0 with ha | ha
    · have hb : 0 ≤ p.eval b := by
        by_contra! hb
        exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos ha hb.le)) h
      exact intermediate_value_Icc hab.le p.differentiable.continuous.continuousOn ⟨ha,hb⟩
    · have hb : p.eval b ≤ 0 := by
        by_contra! hb
        exact (not_lt_of_ge (mul_nonneg ha.le hb.le)) h
      exact intermediate_value_Icc' hab.le p.differentiable.continuous.continuousOn ⟨hb,ha.le⟩
  obtain ⟨r,⟨hl,hr⟩,hz⟩ := hin
  change p.eval r = 0 at hz
  have hneL : a ≠ r := by
    intro he
    rw [he,hz,zero_mul] at h
    exact (lt_irrefl _) h
  have hneR : r ≠ b := by
    intro he
    rw [← he,hz,mul_zero] at h
    exact (lt_irrefl _) h
  exact ⟨r,⟨lt_of_le_of_ne hl hneL, lt_of_le_of_ne hr hneR⟩,hz⟩

/-- Opposite signs on successive gaps account for all roots once there are at least
as many gaps as the degree. In particular all roots are below a common node bound. -/
theorem splits_and_roots_lt_of_alternating_values {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n)
    (points : Fin (n+1) → ℝ) (hmono : StrictMono points)
    (hflip : ∀ i : Fin n, p.eval (points i.castSucc) * p.eval (points i.succ) < 0)
    {bound : ℝ} (hbound : ∀ i, points i ≤ bound) :
    p.Splits ∧ ∀ r ∈ p.roots, r < bound := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  choose root hgap hz using (fun i : Fin n =>
    exists_root_between (hmono i.castSucc_lt_succ) (hflip i))
  have hroots : StrictMono root := by
    intro i j hij
    have hij' : i.succ ≤ j.castSucc := by
      change i.val+1 ≤ j.val
      exact hij
    exact (hgap i).2.trans_le ((hmono.monotone hij').trans (hgap j).1.le)
  have hsub : Finset.univ.image root ⊆ p.roots.toFinset := by
    intro r hr
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hr
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hz i))
  have hcard := Finset.card_le_card hsub
  have himg : (Finset.univ.image root).card = n := by
    rw [Finset.card_image_of_injective _ hroots.injective, Finset.card_univ, Fintype.card_fin]
  have hlow : n ≤ p.roots.card :=
    (himg ▸ hcard).trans (Multiset.toFinset_card_le p.roots)
  have heq : Finset.univ.image root = p.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [himg]
      exact (Multiset.toFinset_card_le _).trans ((card_roots' p).trans hdeg))
  refine ⟨splits_iff_card_roots.mpr (le_antisymm (card_roots' p) (hdeg.trans hlow)), ?_⟩
  intro r hr
  have hr' := Multiset.mem_toFinset.mpr hr
  rw [← heq] at hr'
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr'
  exact (hgap i).2.trans_le (hbound i.succ)

/-- Opposite signs on each of the degree-many successive gaps force splitting. -/
theorem splits_of_alternating_values {p : ℝ[X]} {n : ℕ} (hdeg : p.natDegree = n)
    (points : Fin (n+1) → ℝ) (hmono : StrictMono points)
    (hflip : ∀ i : Fin n, p.eval (points i.castSucc) * p.eval (points i.succ) < 0) :
    p.Splits :=
  (splits_and_roots_lt_of_alternating_values hdeg.le points hmono hflip
    (fun i => hmono.monotone (Fin.le_last i))).1

end JacobiProjective
