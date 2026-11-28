module

public import GaussianContent
public import GaussianAngle
public import SlopeFactorial
public import TangentCount

@[expose] public section

namespace ArctanPole
open Real Finset MollRigidity Chebyshev

/-- Integrality eventually forces the literal tangent past every fixed power. -/
theorem integral_slope_height (r : ℕ) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (gaussProd n).re ∣ (gaussProd n).im → (n:ℝ)^r ≤ |tan (angle n)| := by
  obtain ⟨b,hb⟩ := factorial_saving r
  use max 1 b
  intro n hn h
  have hn0 : 0 < n := (le_max_left 1 b).trans hn
  let P := gaussProd n
  let g := Int.gcd P.re P.im
  obtain ⟨m,hm⟩ := h
  have he := (normBlock_integer_slope hm).2
  change normBlock n = g^2 * (1+m.natAbs^2) at he
  have hg : g ∣ normBlock n := by rw [he, pow_two, mul_assoc]; exact dvd_mul_right _ _
  have hF : g ∣ n.factorial*Nat.lcmUpto (2*n) := (gaussian_content n hn0).trans
    (Nat.mul_dvd_mul_right (Nat.factorial_dvd_factorial (Nat.sub_le n 1)) (Nat.lcmUpto (2*n)))
  have hsmall := hb n ((le_max_right _ _).trans hn) g blockDivisor blockDivisor_lower
    (blockDivisor_joint hg hF)
  have hbig : n.factorial ≤ g*(1+m.natAbs) := by
    have H := factorial_sq_le_normBlock n
    rw [he] at H
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    rw [Nat.mul_pow]
    exact H.trans (Nat.mul_le_mul_left _ (by nlinarith only [Nat.zero_le m.natAbs]))
  have hnat : n^r ≤ m.natAbs := by
    have hu := Nat.lt_of_mul_lt_mul_left (hsmall.trans_le hbig)
    omega
  rw [tangent_of_integer_slope hm]
  calc
    _ ≤ (m.natAbs:ℝ) := by exact_mod_cast hnat
    _ = _ := by simp

/-- Power-saving count for indices satisfying the original Gaussian divisibility
predicate in the arctangent nonintegrality conjecture. -/
theorem integral_index_count : ∃ n₀ : ℕ, ∀ N ≥ n₀, ∀ S : Finset ℕ,
    (∀ n ∈ S, n₀ ≤ n ∧ n ≤ N ∧ (gaussProd n).re ∣ (gaussProd n).im) →
    (S.card:ℝ)^4 ≤ 64^4*(80*log N)^3 := by
  obtain ⟨a,ha⟩ := large_tangent_count
  obtain ⟨b,hb⟩ := integral_slope_height 6
  use max a b
  intro N hN S hS
  apply ha N ((le_max_left _ _).trans hN)
  intro n hn
  obtain ⟨hn₀,hn',hd⟩ := hS n hn
  exact ⟨(le_max_left _ _).trans hn₀,hn',hb n ((le_max_right _ _).trans hn₀) hd⟩

#print axioms integral_index_count

end ArctanPole
