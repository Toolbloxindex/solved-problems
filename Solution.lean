module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Basic.Real.Basic
public import JacobiSourceSeries

@[expose] public section

open scoped PowerSeries

namespace PalomarJacobi

/-- The source diagonal J(n+k,n;u) with its literal triangular recurrence. -/
noncomputable def diagonal (u : ℝ) : ℕ → ℕ → ℝ :=
  Nat.rec (motive := fun _ => ℕ → ℝ) (fun _ => 1) fun _ prev =>
    Nat.rec 0 (fun n acc => acc + ((n+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ)+u) * prev (n+1))

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
  have hcells (u : ℝ) (k : ℕ) : diagonal u k = JacobiDiagonalControls.diagonal u k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change Nat.rec (motive := fun _ => ℝ) 0 (fun n acc => acc + ((n+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ)+u) * diagonal u k (n+1)) = _
      rw [ih]
      rfl
  have hdiag : diagonalSeries = JacobiProjective.diagonalSeries := by
    funext u m
    unfold diagonalSeries JacobiProjective.diagonalSeries
    rw [hcells]
  obtain ⟨ρ, hρ, hd, hh⟩ := JacobiProjective.sharp_nonnegative_source_series
  refine ⟨ρ, hρ, ?_, ?_⟩
  · have hcut := (JacobiDiagonalControls.disc_pos_shift (ρ-2)).symm
    change thresholdPolynomial ρ = JacobiDiagonalControls.disc (2+(ρ-2)) at hcut
    rw [show (2 : ℝ)+(ρ-2)=ρ by ring, hd] at hcut
    exact hcut
  · simpa only [hdiag] using hh

end PalomarJacobi
