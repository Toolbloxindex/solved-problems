module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.QuadraticAlgebra.Defs
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MollRigidity
open Finset
open scoped QuadraticAlgebra

/-- Coordinates with i² = −1, including over non-fields. -/
abbrev Gauss (R : Type*) [CommRing R] := QuadraticAlgebra R (-1) 0

def factor (R : Type*) [CommRing R] (k : ℕ) : Gauss R := ⟨-1, -(k : R)⟩

def state (R : Type*) [CommRing R] : ℕ → Gauss R
  | 0 => 1
  | n+1 => state R n * factor R (n+1)

/-- The product used in the formal statement of the Amdeberhan–Medina–Moll conjecture. -/
def gaussProd (n : ℕ) : Zsqrtd (-1) := ∏ k ∈ Icc 1 n, (⟨1, (k : ℤ)⟩ : Zsqrtd (-1))

def moll (n : ℕ) : ℤ := -((-1 : ℤ) ^ n * (gaussProd n).re)

private theorem state_coords (R : Type*) [CommRing R] (n : ℕ) :
    (state R n).re = (-1 : R)^n * ((gaussProd n).re : R) ∧
    (state R n).im = (-1 : R)^n * ((gaussProd n).im : R) := by
  induction n with
  | zero => simp [state, gaussProd]
  | succ n ih =>
    have h : gaussProd (n+1) = gaussProd n * ⟨1, ((n+1 : ℕ) : ℤ)⟩ :=
      prod_Icc_succ_top (by omega) _
    constructor <;> simp [state, factor, h, Zsqrtd.re_mul, Zsqrtd.im_mul, pow_succ, ih.1, ih.2] <;> ring

theorem moll_mod (m n : ℕ) : (moll n : ZMod m) = -(state (ZMod m) n).re := by
  simp [moll, (state_coords (ZMod m) n).1]

private theorem first {R : Type*} [CommRing R] (n : ℕ) :
    (state R (n+1)).re = -(state R n).re + (n+1 : R) * (state R n).im := by
  simp [state, factor]; ring

private theorem second {R : Type*} [CommRing R] (n : ℕ) :
    (state R (n+2)).re =
      (1 - ((n:R)+1)*((n:R)+2)) * (state R n).re - (2*(n:R)+3)*(state R n).im := by
  simp [state, factor]; ring

private theorem fourth {R : Type*} [CommRing R] (n : ℕ) (him : (state R n).im = 0)
    (hre : (state R n).re = 1) :
    (state R (n+4)).re = (n:R)^4 + 10*(n:R)^3 + 29*(n:R)^2 + 20*(n:R) - 10 := by
  simp [state, factor, him, hre]; ring

private theorem offsets {m t : ℕ} (h : Function.Periodic (fun n => (state (ZMod m) n).re) t) :
    (state (ZMod m) t).re = 1 ∧
    (state (ZMod m) t).im = -(t:ZMod m)*((t:ZMod m)+3) ∧
    (t:ZMod m)*((t:ZMod m)+1)*((t:ZMod m)+3) = 0 := by
  have h0 : (state (ZMod m) t).re = 1 := by simpa [state] using h 0
  have h1 := h 1
  dsimp only at h1
  rw [add_comm 1 t, first] at h1
  have h2 := h 2
  dsimp only at h2
  rw [add_comm 2 t, second] at h2
  simp [h0, state, factor] at h1 h2
  have hi : (state (ZMod m) t).im = -(t:ZMod m)*((t:ZMod m)+3) := by
    linear_combination -h2 - 2*h1
  refine ⟨h0, hi, ?_⟩
  rw [hi] at h1
  linear_combination -h1

/-- Every period from index zero for Moll's signed real part modulo an odd modulus
is a multiple of that modulus. The two Gaussian coordinates then return to (1,0). -/
theorem dvd_period {m t : ℕ} (hm : Odd m)
    (hper : Function.Periodic (fun n => (moll n : ZMod m)) t) :
    m ∣ t ∧ state (ZMod m) t = 1 := by
  have h : Function.Periodic (fun n => (state (ZMod m) n).re) t := by
    intro n
    simpa only [moll_mod, neg_inj] using hper n
  obtain ⟨hr, hi, hx⟩ := offsets h
  have hmpos : 0 < m := by obtain ⟨k,hk⟩ := hm; omega
  have hneg : (((m-1)*t:ℕ) : ZMod m) = -(t:ZMod m) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)]
    simp
  have hy := (offsets (h.nat_mul (m-1))).2.2
  simp only [Nat.cast_id] at hy
  rw [hneg] at hy
  have hu : IsUnit (2 : ZMod m) := (ZMod.isUnit_iff_coprime 2 m).2 hm.coprime_two_left
  have hz : (t:ZMod m)^2 = 0 := by
    apply (hu.pow 3).mul_left_cancel
    linear_combination hx + hy
  have h3 : 3*(t:ZMod m) = 0 := by
    linear_combination hx - ((t:ZMod m)+4)*hz
  have hi0 : (state (ZMod m) t).im = 0 := by linear_combination hi - hz - h3
  have h4 := h 4
  dsimp only at h4
  rw [add_comm 4 t, fourth t hi0 hr] at h4
  have base : (state (ZMod m) 4).re = -10 := by simp [state, factor]; ring
  rw [base] at h4
  have ht : (t:ZMod m) = 0 := by
    linear_combination 7*h3 - h4 + ((t:ZMod m)^2+10*(t:ZMod m)+29)*hz
  exact ⟨(ZMod.natCast_eq_zero_iff t m).mp ht, QuadraticAlgebra.ext hr hi0⟩


theorem block_shift (m n : ℕ) : state (ZMod m) (m+n) = state (ZMod m) m * state (ZMod m) n := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    change state (ZMod m) (m+n) * factor (ZMod m) (m+n+1) = _
    have hf : factor (ZMod m) (m+n+1) = factor (ZMod m) (n+1) := by simp [factor]
    rw [ih, hf, mul_assoc]
    rfl

theorem blocks (m k n : ℕ) :
    state (ZMod m) (m*k+n) = state (ZMod m) m ^ k * state (ZMod m) n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, show m*k+m+n = m+(m*k+n) by omega, block_shift, ih, pow_succ]
    ac_rfl

/-- Exact criterion for every pure period, including odd composite moduli.
Mathlib assigns order zero to a monoid element with no positive power equal to one. -/
theorem period_iff {m t : ℕ} (hm : Odd m) :
    Function.Periodic (fun n => (moll n : ZMod m)) t ↔
      m * orderOf (state (ZMod m) m) ∣ t := by
  constructor
  · intro ht
    obtain ⟨⟨k,rfl⟩, hs⟩ := dvd_period hm ht
    have hk := blocks m k 0
    simp only [Nat.add_zero, state, mul_one] at hk
    exact Nat.mul_dvd_mul_left _ (orderOf_dvd_of_pow_eq_one (hk.symm.trans hs))
  · rintro ⟨k,rfl⟩ n
    dsimp only
    rw [moll_mod, moll_mod, add_comm n, Nat.mul_assoc, blocks, pow_mul, pow_orderOf_eq_one,
      one_pow, one_mul]

end MollRigidity
