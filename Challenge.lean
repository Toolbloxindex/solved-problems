module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.GCDMonoid.Finset

@[expose] public section

namespace PalomarMoll

/-- Moll's Theorem 2.4, including the product's neutral factor at zero. -/
def signedReal (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n + 1) * (∏ k ∈ Finset.Icc 0 n, (⟨1, (k : ℤ)⟩ : Zsqrtd (-1))).re

/-- Equality holds at every index from some cutoff onward. -/
def eventualPeriod (m t : ℕ) : Prop :=
  ∃ cutoff : ℕ, ∀ n ≥ cutoff, (signedReal (n + t) : ZMod m) = signedReal n

/-- The empty lcm is one. The power of each prime is its exact power in the modulus. -/
noncomputable def periodLength (m : ℕ) : ℕ :=
  (m.primeFactors.filter (fun p => p % 4 = 3)).lcm
    (fun p => p ^ m.factorization p * orderOf (-2 : ZMod p))

/-- The least positive eventual period for every positive modulus. -/
theorem least_eventual_period (m : ℕ) (hm : 0 < m) :
    IsLeast {t : ℕ | 0 < t ∧ eventualPeriod m t} (periodLength m) := by
  sorry

/-- Characterization of positive periods valid from index zero. -/
theorem pure_period_iff (m t : ℕ) (hm : 0 < m) (ht : 0 < t) :
    Function.Periodic (fun n => (signedReal n : ZMod m)) t ↔
      (∀ p ∈ m.primeFactors, p % 4 = 3) ∧ periodLength m ∣ t := by
  sorry

end PalomarMoll
