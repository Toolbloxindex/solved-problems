module

public import JacobiInverse
public import Mathlib.RingTheory.PowerSeries.WellKnown

@[expose] public section

open scoped PowerSeries

namespace JacobiProjective

open Polynomial JacobiDiagonalControls

/-- The literal source series for diagonal rank m+1. -/
noncomputable def diagonalSeries (u : ℝ) (m : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk (diagonal u (m+1))

private noncomputable def basisSeries (m i : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.X^(i+1) * (PowerSeries.invOneSubPow ℝ (m+3+i)).val

private theorem coeff_basisSeries (m i n : ℕ) :
    PowerSeries.coeff n (basisSeries m i) = ((n+(m+1)).choose (m+2+i) : ℝ) := by
  unfold basisSeries
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hi : i+1 ≤ n
  · rw [ite_eq_left hi, show m+3+i = (m+2+i)+1 by omega,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk,
      show m+2+i+(n-(i+1)) = n+(m+1) by omega]
  · rw [ite_eq_right hi, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

private theorem diagonalSeries_expansion (u : ℝ) (m : ℕ) :
    diagonalSeries u m =
      ∑ i ∈ (projective u m).support,
        PowerSeries.C ((projective u m).coeff i) * basisSeries m i := by
  ext n
  rw [diagonalSeries, PowerSeries.coeff_mk, diagonal_eq_binomialLift,
    binomialLift, Polynomial.sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [PowerSeries.coeff_C_mul, coeff_basisSeries]

/-- Source normalization in formal power series with exactly the published denominator. -/
theorem sourceNumerator_series (u : ℝ) (m : ℕ) :
    (sourceNumerator u m : ℝ⟦X⟧) =
      (1-PowerSeries.X)^(3*(m+1)+1)*diagonalSeries u m := by
  rw [diagonalSeries_expansion, sourceNumerator,
    inverse_eq_sum (projective u m) (projective_degree_le u m), Polynomial.coe_mul, Polynomial.coe_X]
  change (PowerSeries.X : ℝ⟦X⟧) *
    (coeToPowerSeries.ringHom : ℝ[X] →+* ℝ⟦X⟧) (∑ i ∈ _, _) = _
  rw [map_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : i ≤ 2*m+1 := (le_natDegree_of_mem_supp i hi).trans (projective_degree_le u m)
  have he : 3*(m+1)+1 = (2*m+1-i)+(m+3+i) := by omega
  simp only [coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_one]
  rw [basisSeries, he]
  have hcancel := PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow
    (S := ℝ) (d := 2*m+1-i) (m+3+i)
  rw [show
    (1-PowerSeries.X)^(2*m+1-i+(m+3+i)) *
        (PowerSeries.C ((projective u m).coeff i) *
          (PowerSeries.X^(i+1)*(PowerSeries.invOneSubPow ℝ (m+3+i)).val)) =
      ((1-PowerSeries.X)^(2*m+1-i+(m+3+i))*(PowerSeries.invOneSubPow ℝ (m+3+i)).val) *
        (PowerSeries.C ((projective u m).coeff i)*PowerSeries.X^(i+1)) by ring, hcancel, pow_succ]
  ring

/-- Lin–Zeng's all-rank source numerators, in their original formal series normalization. -/
theorem sharp_nonnegative_source_series :
    ∃ ρ ∈ Set.Ioo (41/20 : ℝ) (33/16), disc ρ = 0 ∧
      ∀ u : ℝ, 0 ≤ u →
        ((∀ m : ℕ, ∃ A : ℝ[X], A.Splits ∧
            (A : ℝ⟦X⟧) = (1-PowerSeries.X)^(3*(m+1)+1)*diagonalSeries u m) ↔
          u ≤ ρ) := by
  obtain ⟨ρ,hρ,hd,h⟩ := sharp_nonnegative_numerator_interval
  refine ⟨ρ,hρ,hd,fun u hu => ?_⟩
  rw [← h u hu]
  constructor
  · intro h₁ m
    obtain ⟨A,hs,he⟩ := h₁ m
    have eq : A = sourceNumerator u m :=
      Polynomial.coe_injective ℝ (he.trans (sourceNumerator_series u m).symm)
    exact eq ▸ hs
  · intro h₁ m
    exact ⟨sourceNumerator u m, h₁ m, sourceNumerator_series u m⟩

end JacobiProjective
