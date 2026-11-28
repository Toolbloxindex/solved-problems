import JacobiRankTwo
import Mathlib.Algebra.CubicDiscriminant

namespace JacobiRankTwoSource

open Polynomial JacobiDiagonalControls JacobiRankTwo Set

private instance : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective

private noncomputable def reduced (u : ℝ) : Cubic ℝ :=
  ⟨2*(2-u)*(1-u), 21-6*u-3*u^2, 14+10*u, (1+u)^2⟩

/-- The literal second-diagonal numerator in Lin–Zeng's denominator convention. -/
noncomputable def secondNumerator (u : ℝ) : ℝ[X] := X * (reduced u).toPoly

theorem reduced_eval (u x : ℝ) : (reduced u).toPoly.eval x = f2 u x := by
  simp [reduced, Cubic.toPoly, f2]
  ring

theorem secondNumerator_eval (u x : ℝ) : (secondNumerator u).eval x = x * f2 u x := by
  simp [secondNumerator, reduced_eval]

private theorem b_ne_zero_of_a_zero {u : ℝ} (ha : (reduced u).a = 0) :
    (reduced u).b ≠ 0 := by
  change 2*(2-u)*(1-u) = 0 at ha
  rcases mul_eq_zero.mp ha with h | h
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · have hu : u = 2 := by linarith
      norm_num [hu, reduced]
  · have hu : u = 1 := by linarith
    norm_num [hu, reduced]

theorem splits_iff_factors (u : ℝ) : (secondNumerator u).Splits ↔ factors u := by
  rw [secondNumerator, splits_X_mul]
  change (reduced u).toPoly.Splits ↔
    if (reduced u).a = 0 then
      ∃ r s : ℝ, ∀ x : ℝ, f2 u x = (reduced u).b*(x-r)*(x-s)
    else
      ∃ r s t : ℝ, ∀ x : ℝ, f2 u x = (reduced u).a*(x-r)*(x-s)*(x-t)
  split
  · rename_i ha
    have hb := b_ne_zero_of_a_zero ha
    constructor
    · intro hs
      have hcard : (reduced u).toPoly.roots.card = 2 :=
        hs.natDegree_eq_card_roots.symm.trans (Cubic.natDegree_of_b_ne_zero ha hb)
      obtain ⟨r,s,hroots⟩ := Multiset.card_eq_two.mp hcard
      refine ⟨r,s,fun x => ?_⟩
      have hx := hs.eval_eq_prod_roots x
      rw [reduced_eval, Cubic.leadingCoeff_of_b_ne_zero ha hb, hroots] at hx
      simpa [mul_assoc] using hx
    · rintro ⟨r,s,h⟩
      have hp : (reduced u).toPoly = C (reduced u).b * (X-C r) * (X-C s) :=
        Polynomial.funext (fun x => by simpa [reduced_eval] using h x)
      rw [hp]
      exact (((Splits.C _).mul (Splits.X_sub_C r)).mul (Splits.X_sub_C s))
  · rename_i ha
    constructor
    · intro hs
      have hcard : (reduced u).toPoly.roots.card = 3 :=
        hs.natDegree_eq_card_roots.symm.trans (Cubic.natDegree_of_a_ne_zero ha)
      obtain ⟨r,s,t,hroots⟩ := Multiset.card_eq_three.mp hcard
      refine ⟨r,s,t,fun x => ?_⟩
      have hx := hs.eval_eq_prod_roots x
      rw [reduced_eval, Cubic.leadingCoeff_of_a_ne_zero ha, hroots] at hx
      simpa [mul_assoc] using hx
    · rintro ⟨r,s,t,h⟩
      have hp : (reduced u).toPoly = C (reduced u).a * (X-C r) * (X-C s) * (X-C t) :=
        Polynomial.funext (fun x => by simpa [reduced_eval] using h x)
      rw [hp]
      exact ((((Splits.C _).mul (Splits.X_sub_C r)).mul (Splits.X_sub_C s)).mul (Splits.X_sub_C t))

/-- Over all real parameters, the second Jacobi–Stirling diagonal numerator splits
over the reals exactly on the interval between the two indicated discriminant zeros. -/
theorem secondNumerator_splits_sharp :
    ∃ left ∈ Ioo (-(121/100) : ℝ) (-(6/5)),
      ∃ right ∈ Ioo (41/20 : ℝ) (33/16),
        disc left = 0 ∧ disc right = 0 ∧
          ∀ u : ℝ, (secondNumerator u).Splits ↔ left ≤ u ∧ u ≤ right := by
  obtain ⟨l, hl, r, hr, hdl, hdr, h⟩ := rank_two_sharp
  exact ⟨l, hl, r, hr, hdl, hdr, fun u => (splits_iff_factors u).trans (h u)⟩

end JacobiRankTwoSource
