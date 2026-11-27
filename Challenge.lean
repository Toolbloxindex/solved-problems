module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PalomarStirling

namespace FirstColumn

def qmul (a : Int → Int) (d : Int) : Nat → Int
  | 0 => 0
  | w+1 => qmul a d w + a (d-(w:Int))

def sb : Nat → Nat → Int → Int
  | 0,k,d => if k=0 ∧ d=0 then 1 else 0
  | n+1,0,d => qmul (sb n 0) d 1
  | n+1,k+1,d => sb n k d + qmul (sb n (k+1)) d (2*(k+1)+1)

def StrictInterior (n : Nat) (a : Int → Int) :=
  ∀ d : Int, 0 < d → d < 2*(n : Int)-2 → a (d-1) * a (d+1) < a d ^ 2

theorem original_column_strict_iff (n : Nat) :
    StrictInterior n (sb n 1) ↔ n ≤ 1 ∨ 6 ≤ n := by
  sorry

theorem original_column_five_equality_iff (d : Int) (hl : 0 < d) (hr : d < 8) :
    sb 5 1 (d-1) * sb 5 1 (d+1) = sb 5 1 d ^ 2 ↔ d = 1 := by
  sorry
end FirstColumn

namespace StirlingRecurrence
open _root_.PalomarStirling.FirstColumn (qmul sb)

def cb : Nat → Nat → Int → Int
  | 0, k, d => if k = 0 ∧ d = 0 then 1 else 0
  | n+1, 0, d => qmul (cb n 0) d (2*n+1)
  | n+1, k+1, d => cb n k d + qmul (cb n (k+1)) d (2*n+1)

def coeff (first : Bool) := if first then cb else sb

def degree (first : Bool) (n k : Nat) : Int :=
  if first then (n:Int)*((n:Int)-1) - (k:Int)*((k:Int)-1)
  else 2*(k:Int)*((n:Int)-(k:Int))

theorem recurrence_support (first : Bool) (n k : Nat) (hk : k ≤ n) (d : Int) :
    (0 < coeff first n k d ↔ 0 ≤ d ∧ d ≤ degree first n k) ∧
    (coeff first n k d = 0 ↔ d < 0 ∨ degree first n k < d) := by
  sorry

theorem recurrence_second_parity (first : Bool) (n : Nat) (hn : 2 ≤ n) (d : Int) :
    coeff first n (n-2) d * coeff first n (n-2) (d+4) ≤
      coeff first n (n-2) (d+2)^2 := by
  sorry
end StirlingRecurrence

namespace StirlingBoxes.OmissionCenter
open _root_.PalomarStirling.StirlingRecurrence

def center : ℕ → ℤ
  | 0 => 0
  | n+1 => center n+n

theorem column_one_rising_gap (r : ℕ) (d s : ℤ) (hs : 0≤s)
    (rise : cb (r+1) 1 (d-s)≤cb (r+1) 1 (d+s)) :
    cb (r+1) 1 (d-s)*cb (r+1) 1 (d+s)≤cb (r+1) 1 d^2 := by
  sorry

theorem column_one_lower_parity (r : ℕ) (d : ℤ)
    (low : d≤center r ∨ d+1<center (r+1)) :
    cb (r+1) 1 (d-2)*cb (r+1) 1 (d+2)≤cb (r+1) 1 d^2 := by
  sorry

theorem column_one_unimodal (r : ℕ) :
    ∃ p : ℤ, center r≤p ∧ p≤center (r+1) ∧
      (∀ x : ℤ, x<p → cb (r+1) 1 x≤cb (r+1) 1 (x+1)) ∧
      (∀ x : ℤ, p≤x → cb (r+1) 1 (x+1)≤cb (r+1) 1 x) := by
  sorry
end StirlingBoxes.OmissionCenter

end PalomarStirling
