module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Push

@[expose] public section

namespace ArctanPole
open Finset

/-- Product of the norms of the first Gaussian factors. -/
def normBlock : ℕ → ℕ
  | 0 => 1
  | k+1 => normBlock k * (1+(k+1)^2)

theorem normBlock_eq (n : ℕ) :
    normBlock n = ∏ k ∈ range n, (1+(k+1)^2) := by
  induction n with
  | zero => simp [normBlock]
  | succ n ih => simp [normBlock, prod_range_succ, ih]

private theorem factor_dvd_normBlock {b k : ℕ} (hk : 1 ≤ k) (hb : k ≤ b) :
    1+k^2 ∣ normBlock b := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [normBlock_eq]
  exact dvd_prod_of_mem (fun i => 1+(i+1)^2) (mem_range.mpr (by omega : j < b))

/-- A divisor of 1024! supported on its primes congruent to 3 modulo 4.
The exponent of each listed prime is its exponent in 1024!. -/
def blockDivisor : ℕ :=
  3^508 * 7^168 * 11^101 * 19^55 * 23^45 * 31^34 * 43^23 * 47^21 * 59^17 * 67^15 *
  71^14 * 79^12 * 83^12 * 103^9 * 107^9 * 127^8 * 131^7 * 139^7 * 151^6 * 163^6 *
  167^6 * 179^5 * 191^5 * 199^5 * 211^4 * 223^4 * 227^4 * 239^4 * 251^4 * 263^3 *
  271^3 * 283^3 * 307^3 * 311^3 * 331^3 * 347^2 * 359^2 * 367^2 * 379^2 * 383^2 *
  419^2 * 431^2 * 439^2 * 443^2 * 463^2 * 467^2 * 479^2 * 487^2 * 491^2 * 499^2 *
  503^2 * 523 * 547 * 563 * 571 * 587 * 599 * 607 * 619 * 631 *
  643 * 647 * 659 * 683 * 691 * 719 * 727 * 739 * 743 * 751 *
  787 * 811 * 823 * 827 * 839 * 859 * 863 * 883 * 887 * 907 *
  911 * 919 * 947 * 967 * 971 * 983 * 991 * 1019

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem block_check :
    2^4361 ≤ blockDivisor ∧ blockDivisor ∣ Nat.factorial 1024 ∧
      blockDivisor.Coprime (normBlock 1024) := by decide +kernel

private theorem prime_le_of_dvd_fac {p : ℕ} (hp : p.Prime) :
    ∀ n, p ∣ Nat.factorial n → p ≤ n := by
  intro n
  induction n with
  | zero => simp [Nat.factorial_zero, hp.not_dvd_one]
  | succ n ih =>
    intro h
    rw [Nat.factorial_succ, hp.dvd_mul] at h
    rcases h with h|h
    · exact Nat.le_of_dvd (by omega) h
    · exact (ih h).trans (Nat.le_succ _)

theorem blockDivisor_coprime_factor (k : ℕ) : blockDivisor.Coprime (1+k^2) := by
  by_contra h
  obtain ⟨p,hp,hd,hk⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hb := prime_le_of_dvd_fac hp _ (hd.trans block_check.2.1)
  let r := k%p
  have hr : r < p := Nat.mod_lt k hp.pos
  have hm : p ∣ 1+r^2 := by
    have H : r ≡ k [MOD p] := Nat.mod_modEq k p
    exact Nat.modEq_zero_iff_dvd.mp (((H.pow 2).add_left 1).trans (Nat.modEq_zero_iff_dvd.mpr hk))
  have hr' : 1 ≤ r := by
    by_contra! h
    have : r = 0 := by omega
    simp [this,hp.not_dvd_one] at hm
  have hz := hm.trans (factor_dvd_normBlock hr' (by omega : r ≤ 1024))
  exact (hp.coprime_iff_not_dvd.mp (block_check.2.2.coprime_dvd_left hd)) hz

theorem blockDivisor_coprime (n : ℕ) : blockDivisor.Coprime (normBlock n) := by
  rw [normBlock_eq]
  exact Nat.coprime_prod_right_iff.mpr (fun k _ => blockDivisor_coprime_factor (k+1))

/-- The fixed certified divisor occurs once in every full factorial block. -/
theorem blockDivisor_pow_dvd (n : ℕ) : blockDivisor ^ (n/1024) ∣ n.factorial := by
  have h (q : ℕ) : blockDivisor^q ∣ (1024*q).factorial := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [pow_succ, Nat.mul_succ]
      exact (Nat.mul_dvd_mul ih block_check.2.1).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  exact (h _).trans (Nat.factorial_dvd_factorial (Nat.mul_div_le n 1024))

/-- Simultaneous divisibility by both the common divisor and the inert factorial part. -/
theorem blockDivisor_joint {n g L : ℕ} (hg : g ∣ normBlock n) (hf : g ∣ n.factorial*L) :
    g * blockDivisor^(n/1024) ∣ n.factorial*L :=
  ((blockDivisor_coprime n).symm.coprime_dvd_left hg).pow_right _ |>.mul_dvd_of_dvd_of_dvd hf
    ((blockDivisor_pow_dvd n).trans (Nat.dvd_mul_right ..))

theorem blockDivisor_lower : 2^4361 ≤ blockDivisor := block_check.1

#print axioms blockDivisor_joint
#print axioms blockDivisor_lower

end ArctanPole
