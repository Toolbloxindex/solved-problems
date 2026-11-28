module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Basic.Real.Basic

@[expose] public section

open scoped PowerSeries

namespace PalomarJacobi

/-- The source diagonal J(n+k,n;u) with its literal triangular recurrence. -/
noncomputable def diagonal (u : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | k+1 => Nat.rec 0 (fun n acc =>
      acc + ((n+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ)+u) * diagonal u k (n+1))

/-- The power series for the positive rank m+1. -/
noncomputable def diagonalSeries (u : ℝ) (m : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk (diagonal u (m+1))

/-- The published discriminant written as a polynomial in u-2. -/
noncomputable def thresholdPolynomial (u : ℝ) : ℝ :=
  let s := u-2
  11376-198368*s-274352*s^2-164928*s^3-53744*s^4-9440*s^5-720*s^6

theorem nonnegative_threshold :
    ∃ ρ ∈ Set.Ioo (41/20 : ℝ) (33/16), thresholdPolynomial ρ = 0 ∧
      ∀ u : ℝ, 0 ≤ u →
        ((∀ m : ℕ, ∃ A : Polynomial ℝ, A.Splits ∧
            (A : ℝ⟦X⟧) = (1-PowerSeries.X)^(3*(m+1)+1)*diagonalSeries u m) ↔
          u ≤ ρ) := by
  sorry

end PalomarJacobi
