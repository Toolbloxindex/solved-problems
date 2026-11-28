module

public import JacobiDiagonalControls
public import JacobiPropagation
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

namespace JacobiProjective

open Polynomial JacobiDiagonalControls

/-- Coefficients in the binomial basis associated to the projective substitution. -/
noncomputable def binomialLift (top lower : ℕ) (p : ℝ[X]) : ℝ :=
  p.sum fun i c => c * (top.choose (lower+i) : ℝ)

theorem binomialLift_add (top lower : ℕ) (p q : ℝ[X]) :
    binomialLift top lower (p+q) = binomialLift top lower p + binomialLift top lower q := by
  unfold binomialLift
  rw [Polynomial.sum_add_index]
  · intro i; exact zero_mul _
  · intro i a b; exact add_mul _ _ _

theorem binomialLift_monomial (top lower i : ℕ) (c : ℝ) :
    binomialLift top lower (monomial i c) = c * (top.choose (lower+i) : ℝ) := by
  unfold binomialLift
  rw [sum_monomial_index]
  exact zero_mul _

private theorem choose_linear (top low : ℕ) :
    ((top : ℝ) - low) * (top.choose low : ℝ) =
      ((low : ℝ)+1) * (top.choose (low+1) : ℝ) := by
  by_cases ht : low ≤ top
  · exact_mod_cast (by
      rw [← Nat.cast_sub ht]
      norm_cast
      exact ((Nat.choose_succ_right_eq top low).trans (Nat.mul_comm _ _)).symm.trans
        (Nat.mul_comm _ _) :
      ((top : ℝ) - low) * (top.choose low : ℝ) =
        ((low : ℝ)+1) * (top.choose (low+1) : ℝ))
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge ht),
      Nat.choose_eq_zero_of_lt ((lt_of_not_ge ht).trans (Nat.lt_succ_self low))]
    simp

theorem step_add (a b : ℝ) (p q : ℝ[X]) :
    step a b (p+q) = step a b p + step a b q := by
  simp [step, mul_add]
  ring

private theorem step_monomial (a b c : ℝ) (i : ℕ) :
    step a b (monomial i c) =
      monomial i ((i+a)*c) + monomial (i+1) ((i+b)*c) := by
  have h : X * (monomial i c).derivative = monomial i ((i : ℝ)*c) := by
    cases i with
    | zero => simp
    | succ i =>
      rw [derivative_monomial_succ, X_mul_monomial, Nat.cast_succ, mul_comm]
  rw [step, mul_comm X (1+X), mul_assoc, h, add_mul, one_mul, X_mul_monomial,
    add_mul, mul_assoc, X_mul_monomial, C_mul_monomial, C_mul_monomial,
    add_add_add_comm, ← map_add, ← map_add, add_mul, add_mul]

/-- Multiplication by the series index plus a shift in the binomial representation. -/
theorem binomialLift_step (top lower : ℕ) (c : ℝ) (p : ℝ[X]) :
    binomialLift top lower (step (1+c) ((lower : ℝ)+1) p) =
      ((top : ℝ) - lower + 1 + c) * binomialLift top lower p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [step_add, binomialLift_add, hp, hq, binomialLift_add, mul_add]
  | monomial i a =>
    rw [step_monomial, binomialLift_add]
    simp only [binomialLift_monomial]
    have hh := choose_linear top (lower+i)
    simp only [Nat.cast_add] at hh
    rw [← Nat.add_assoc]
    linear_combination -a*hh

/-- Pascal's rule converts the difference in the diagonal index to an adjacent lower basis. -/
theorem binomialLift_pascal (top lower : ℕ) (p : ℝ[X]) :
    binomialLift (top+1) (lower+1) p =
      binomialLift top lower p + binomialLift top (lower+1) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [binomialLift_add, hp, hq]
    ring
  | monomial i a =>
    simp only [binomialLift_monomial]
    rw [show lower+1+i = (lower+i)+1 by omega, Nat.choose_succ_succ, Nat.cast_add, mul_add]

/-- Representation of the k-th projective numerator with index k−1. -/
noncomputable def projective (u : ℝ) : ℕ → ℝ[X]
  | 0 => monomial 0 (1+u) + monomial 1 2
  | m+1 => step 1 ((m : ℝ)+3) (step (1+u) ((m : ℝ)+3) (projective u m))

theorem projective_step_splits {u : ℝ} {m : ℕ} (hu : 0 ≤ u) (hmargin : u < (m : ℝ)+2)
    (hp : (projective u m).Splits) (hneg : ∀ r ∈ (projective u m).roots, r < 0) :
    (projective u (m+1)).Splits ∧ ∀ r ∈ (projective u (m+1)).roots, r < 0 := by
  obtain ⟨h₁,h₂⟩ :=
    step_splits_negative (a := 1+u) (b := (m : ℝ)+3) (by linarith) (by linarith) hp hneg
  have hm : (0 : ℝ) ≤ m := by positivity
  exact step_splits_negative (a := 1) (b := (m : ℝ)+3) (by norm_num) (by linarith) h₁ h₂

theorem all_projective_from_rank_two {u : ℝ} (hu : 0 ≤ u) (h₃ : u < 3)
    (hbase : (projective u 1).Splits)
    (hneg : ∀ r ∈ (projective u 1).roots, r < 0) (k : ℕ) :
    (projective u (k+1)).Splits ∧ ∀ r ∈ (projective u (k+1)).roots, r < 0 := by
  induction k with
  | zero => exact ⟨hbase, hneg⟩
  | succ k ih =>
    have hn : (0 : ℝ) ≤ k := by positivity
    have hm : u < ((k+1 : ℕ) : ℝ)+2 := by rw [Nat.cast_succ]; linarith
    exact projective_step_splits hu hm ih.1 ih.2

private theorem lift_lt_lower {top lower : ℕ} (h : top < lower) (p : ℝ[X]) :
    binomialLift top lower p = 0 := by
  unfold binomialLift Polynomial.sum
  apply Finset.sum_eq_zero
  intro i _
  change p.coeff i * (top.choose (lower+i) : ℝ) = 0
  rw [Nat.choose_eq_zero_of_lt (show top < lower+i by omega)]
  simp

/-- The projective polynomials reproduce every entry in the literal source diagonal. -/
theorem diagonal_eq_binomialLift (u : ℝ) (m n : ℕ) :
    diagonal u (m+1) n = binomialLift (n+(m+1)) (m+2) (projective u m) := by
  induction m generalizing n with
  | zero =>
    induction n with
    | zero => exact (lift_lt_lower (by decide) _).symm
    | succ n ih =>
      change diagonal u 1 n + ((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+u)*1 =
        binomialLift (n+1+1) 2 (projective u 0)
      rw [Nat.cast_succ, mul_one, ih, binomialLift_pascal (n+1) 1]
      have hh := choose_linear (n+1) 1
      simp only [projective, binomialLift_add, binomialLift_monomial]
      norm_num [Nat.choose_one_right, Nat.cast_succ] at hh ⊢
      linear_combination hh
  | succ m ihm =>
    induction n with
    | zero => exact (lift_lt_lower (by omega) _).symm
    | succ n ihn =>
      change diagonal u (m+2) n +
          ((((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)+u))*diagonal u (m+1) (n+1) =
        binomialLift (n+1+(m+2)) (m+2+1) (projective u (m+1))
      rw [Nat.cast_succ, ihn, ihm, show n+1+(m+1)=n+(m+2) by omega,
        show n+1+(m+2)=(n+(m+2))+1 by omega, binomialLift_pascal]
      have hproj : projective u (m+1) =
          step (1+0) (((m+2 : ℕ) : ℝ)+1)
            (step (1+u) (((m+2 : ℕ) : ℝ)+1) (projective u m)) := by
        simp only [projective, Nat.cast_add, Nat.cast_ofNat, add_zero]
        ring
      rw [hproj, binomialLift_step, binomialLift_step]
      simp only [Nat.cast_add, add_zero]
      ring

end JacobiProjective
