import SlopeGrowth
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith

namespace ArctanPole
open Real Chebyshev

/-- A joint bound on Gaussian content and a large fixed divisor of each factorial
block gives more than any fixed polynomial saving in the normalized product. -/
theorem factorial_saving (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ g D : ℕ, 2^4361 ≤ D →
      g*D^(n/1024) ∣ n.factorial*Nat.lcmUpto (2*n) →
      g*n^r < n.factorial := by
  obtain ⟨b,hb⟩ := block_growth r
  use max 1 b
  intro n hn g D hD hd
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn' : 1 ≤ ((2*n:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ 2*n by omega)
  have hc := psi_le hn'
  rw [psi_eq_log_lcmUpto] at hc
  push_cast at hc
  have hl := hb n ((le_max_right _ _).trans hn) (Nat.lcmUpto (2*n)) (Nat.lcmUpto_pos _) hc
  have hN : Nat.lcmUpto (2*n) * n^r < 2^(4361*(n/1024)) := by exact_mod_cast hl
  rw [pow_mul] at hN
  have hdN := hN.trans_le (Nat.pow_le_pow_left hD _)
  have hsize := Nat.le_of_dvd (Nat.mul_pos (Nat.factorial_pos n) (Nat.lcmUpto_pos _)) hd
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp [Nat.factorial_pos]
  apply Nat.lt_of_mul_lt_mul_right (a:=Nat.lcmUpto (2*n))
  calc
    (g*n^r)*Nat.lcmUpto (2*n) = g*(Nat.lcmUpto (2*n)*n^r) := by ac_rfl
    _ < g*D^(n/1024) := Nat.mul_lt_mul_of_pos_left hdN hg
    _ ≤ _ := hsize

#print axioms factorial_saving

end ArctanPole
