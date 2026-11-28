import JacobiBinomialBridge
import JacobiRankTwo

namespace JacobiProjective

open Polynomial JacobiDiagonalControls JacobiRankTwo

private instance : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective

theorem projective_second_eval (u y : ℝ) :
    (projective u 1).eval y =
      (1+u)^2 + (17+16*u+3*u^2)*y + (52+20*u)*y^2 + 40*y^3 := by
  simp [projective, step, derivative_add, derivative_mul]
  ring

private theorem projective_second_homogeneous (u y : ℝ) :
    (projective u 1).eval y =
      (1+u)^2*(1+y)^3 + (14+10*u)*y*(1+y)^2 +
        (21-6*u-3*u^2)*y^2*(1+y) + 2*(2-u)*(1-u)*y^3 := by
  rw [projective_second_eval]
  ring

private theorem projective_second_eval_off_pole (u y : ℝ) (hy : 1+y ≠ 0) :
    (projective u 1).eval y = (1+y)^3 * f2 u (y/(1+y)) := by
  rw [projective_second_homogeneous]
  unfold f2
  field_simp

private noncomputable def movedRoot (r : ℝ) : ℝ[X] := X-C r*(1+X)

private theorem movedRoot_splits (r : ℝ) : (movedRoot r).Splits := by
  have he : movedRoot r = C (1-r)*X-C r := by
    simp [movedRoot, C_sub]
    ring
  rw [he]
  apply Splits.of_natDegree_le_one
  have hd : (C (1-r)*X).natDegree ≤ 1 := by
    calc
      _ ≤ (C (1-r)).natDegree + (X : ℝ[X]).natDegree := natDegree_mul_le
      _ = 1 := by simp
  have hc : (C r).natDegree ≤ 1 := by rw [natDegree_C]; decide
  exact natDegree_sub_le_of_le hd hc

theorem projective_second_splits {u : ℝ} (h : 0 ≤ disc u) : (projective u 1).Splits := by
  have hf := (factors_iff_disc u).mpr h
  unfold factors at hf
  dsimp only at hf
  split at hf
  · rename_i ha
    obtain ⟨r,s,hf⟩ := hf
    have he : projective u 1 = C (21-6*u-3*u^2) * (1+X) * movedRoot r * movedRoot s := by
      apply Polynomial.funext
      intro y
      simp only [movedRoot, eval_mul, eval_sub, eval_add, eval_one, eval_X, eval_C]
      by_cases hy : 1+y = 0
      · rw [projective_second_homogeneous, hy, ha]
        ring
      · rw [projective_second_eval_off_pole u y hy, hf]
        field_simp
    rw [he]
    have hlin : (1+X : ℝ[X]).Splits := by simpa [add_comm] using Splits.X_add_C (1 : ℝ)
    exact (((Splits.C _).mul hlin).mul (movedRoot_splits r)).mul (movedRoot_splits s)
  · obtain ⟨r,s,t,hf⟩ := hf
    have he : projective u 1 = C (2*(2-u)*(1-u)) * movedRoot r * movedRoot s * movedRoot t := by
      apply Polynomial.funext
      intro y
      simp only [movedRoot, eval_mul, eval_sub, eval_add, eval_one, eval_X, eval_C]
      by_cases hy : 1+y = 0
      · rw [projective_second_homogeneous, hy]
        ring
      · rw [projective_second_eval_off_pole u y hy, hf]
        field_simp
    rw [he]
    exact (((Splits.C _).mul (movedRoot_splits r)).mul (movedRoot_splits s)).mul (movedRoot_splits t)

theorem projective_second_roots_neg {u : ℝ} (hu : 0 ≤ u) :
    ∀ r ∈ (projective u 1).roots, r < 0 := by
  intro r hr
  by_contra! h
  have hzero : (projective u 1).eval r = 0 := isRoot_of_mem_roots hr
  rw [projective_second_eval] at hzero
  have hpos : 0 < (1+u)^2 + (17+16*u+3*u^2)*r + (52+20*u)*r^2 + 40*r^3 := by
    positivity
  linarith

/-- The split property on the exact second diagonal propagates to all higher projective
numerators in the nonnegative parameter range below three. -/
theorem projective_splits_for_cutoff {u : ℝ} (hu : 0 ≤ u) (h₃ : u < 3)
    (hdisc : 0 ≤ disc u) (k : ℕ) :
    (projective u (k+1)).Splits ∧ ∀ r ∈ (projective u (k+1)).roots, r < 0 :=
  all_projective_from_rank_two hu h₃ (projective_second_splits hdisc)
    (projective_second_roots_neg hu) k

end JacobiProjective
