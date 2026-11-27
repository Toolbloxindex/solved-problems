module

public import OmissionRising
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

private theorem qmul_eq : qmul = _root_.FirstColumn.qmul := by
  funext a d w
  induction w with
  | zero => rfl
  | succ w ih => simp only [qmul, _root_.FirstColumn.qmul, ih]

theorem sb_eq : sb = _root_.FirstColumn.sb := by
  funext n k d
  induction n generalizing k d with
  | zero => rfl
  | succ n ih =>
    have row : sb n = _root_.FirstColumn.sb n := funext (fun k => funext (ih k))
    cases k <;> simp only [sb, _root_.FirstColumn.sb, qmul_eq, row]

private theorem strict_eq : StrictInterior = _root_.FirstColumn.StrictInterior := by
  rfl

theorem original_column_strict_iff (n : Nat) :
    StrictInterior n (sb n 1) ↔ n ≤ 1 ∨ 6 ≤ n := by
  rw [strict_eq, sb_eq]
  exact _root_.FirstColumn.original_column_strict_iff n

theorem original_column_five_equality_iff (d : Int) (hl : 0 < d) (hr : d < 8) :
    sb 5 1 (d-1) * sb 5 1 (d+1) = sb 5 1 d ^ 2 ↔ d = 1 := by
  rw [sb_eq]
  exact _root_.FirstColumn.original_column_five_equality_iff d hl hr
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

theorem cb_eq : cb = _root_.StirlingRecurrence.cb := by
  funext n k d
  induction n generalizing k d with
  | zero => rfl
  | succ n ih =>
    have row : cb n = _root_.StirlingRecurrence.cb n := funext (fun k => funext (ih k))
    cases k <;> simp only [cb, _root_.StirlingRecurrence.cb, FirstColumn.qmul_eq, row]

private theorem coeff_eq : coeff = _root_.StirlingRecurrence.coeff := by
  funext first
  cases first <;> simp [coeff, _root_.StirlingRecurrence.coeff, cb_eq, FirstColumn.sb_eq]

private theorem degree_eq : degree = _root_.StirlingRecurrence.degree := by rfl

theorem recurrence_support (first : Bool) (n k : Nat) (hk : k ≤ n) (d : Int) :
    (0 < coeff first n k d ↔ 0 ≤ d ∧ d ≤ degree first n k) ∧
    (coeff first n k d = 0 ↔ d < 0 ∨ degree first n k < d) := by
  rw [coeff_eq, degree_eq]
  exact _root_.StirlingRecurrence.recurrence_support first n k hk d

theorem recurrence_second_parity (first : Bool) (n : Nat) (hn : 2 ≤ n) (d : Int) :
    coeff first n (n-2) d * coeff first n (n-2) (d+4) ≤
      coeff first n (n-2) (d+2)^2 := by
  rw [coeff_eq]
  exact _root_.StirlingRecurrence.recurrence_second_parity first n hn d
end StirlingRecurrence

namespace StirlingBoxes.OmissionCenter
open _root_.PalomarStirling.StirlingRecurrence

def center : ℕ → ℤ
  | 0 => 0
  | n+1 => center n+n

private theorem center_eq : center = _root_.StirlingBoxes.OmissionCenter.center := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp only [center, _root_.StirlingBoxes.OmissionCenter.center, ih]

theorem column_one_rising_gap (r : ℕ) (d s : ℤ) (hs : 0≤s)
    (rise : cb (r+1) 1 (d-s)≤cb (r+1) 1 (d+s)) :
    cb (r+1) 1 (d-s)*cb (r+1) 1 (d+s)≤cb (r+1) 1 d^2 := by
  rw [cb_eq] at *
  exact _root_.StirlingBoxes.OmissionCenter.column_one_rising_gap r d s hs rise

theorem column_one_lower_parity (r : ℕ) (d : ℤ)
    (low : d≤center r ∨ d+1<center (r+1)) :
    cb (r+1) 1 (d-2)*cb (r+1) 1 (d+2)≤cb (r+1) 1 d^2 := by
  rw [center_eq] at low
  rw [cb_eq]
  exact _root_.StirlingBoxes.OmissionCenter.column_one_lower_parity r d low

theorem column_one_unimodal (r : ℕ) :
    ∃ p : ℤ, center r≤p ∧ p≤center (r+1) ∧
      (∀ x : ℤ, x<p → cb (r+1) 1 x≤cb (r+1) 1 (x+1)) ∧
      (∀ x : ℤ, p≤x → cb (r+1) 1 (x+1)≤cb (r+1) 1 x) := by
  rw [center_eq, cb_eq]
  exact _root_.StirlingBoxes.OmissionCenter.column_one_unimodal r
end StirlingBoxes.OmissionCenter

end PalomarStirling
