module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

namespace MollRigidity
open Finset
def gaussProd (n : ℕ) : Zsqrtd (-1) := ∏ k ∈ Icc 1 n, (⟨1, (k : ℤ)⟩ : Zsqrtd (-1))
end MollRigidity


namespace ArctanPole
open Real Finset MollRigidity Filter Asymptotics

/-- Number of integral values in the conjectured empty interval, including its finite prefix. -/
def integralCount (N : ℕ) : ℕ :=
  ((Icc 5 N).filter fun n => (gaussProd n).re ∣ (gaussProd n).im).card

/-- A sublogarithmic upper bound on the count for the original divisibility predicate. -/
theorem integral_count_isBigO :
    (fun N : ℕ => (integralCount N : ℝ)) =O[atTop]
      (fun N : ℕ => (log (N:ℝ)) ^ (3/4 : ℝ)) := by sorry
end ArctanPole
