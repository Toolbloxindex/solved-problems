module

public import PoleCube
public import PoleCount

@[expose] public section

namespace ArctanPole
open Finset

def atCorners (y : ℕ → ℤ) (a h k : ℕ) : IntCorners :=
  ⟨y a, y (a+h), y (a+k), y (a+h+k)⟩

private theorem fits_rectangle {S : Finset ℕ} {y : ℕ → ℤ} {K C q : ℝ}
    (hfit : ∀ i ∈ S, Fits K (C*q^i) (y i)) {a h k : ℕ} (box : HasRectangle S a h k) :
    (atCorners y a h k).FitsAt K (C*q^a) (q^h) (q^k) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := box
  dsimp [IntCorners.FitsAt, atCorners]
  exact ⟨hfit _ h₀, by simpa only [pow_add, mul_assoc] using hfit _ h₁,
    by simpa only [pow_add, mul_assoc] using hfit _ h₂,
    by simpa only [pow_add, mul_assoc] using hfit _ h₃⟩

/-- Dyadic block bound on every finite set of pole labels carrying integer observations
with a common inverse expansion. For the arctangent application the observations are 2n+1,
q = exp(π/2), and C = exp(-c₀). -/
theorem pole_block_count {S : Finset ℕ} {y : ℕ → ℤ} {K C q : ℝ} {J : ℕ}
    (hJ : ∀ i ∈ S, J ≤ i ∧ i < 2*J) (hC : 0 < C) (hq : 2 ≤ q)
    (hstart : 1 ≤ C*q^J) (herror : 1000*budget K ≤ (C*q^J)^2)
    (hwidth : q^J ≤ (C*q^J)^2) (hfit : ∀ i ∈ S, Fits K (C*q^i) (y i)) :
    S.card*S.card ≤ 2*J + 2*(2*J)*Nat.sqrt (3*(2*J)) := by
  apply cube_free_count (fun i hi => mem_range.mpr (hJ i hi).2)
  intro a h k l hh hk hl box box'
  have ha := (hJ a box.1).1
  have htop := (hJ _ box'.2.2.2).2
  have hsum : h+k ≤ J := by omega
  have hq1 : 1 ≤ q := by linarith
  have hp (x : ℕ) (hx : 0 < x) : 2 ≤ q^x := by
    calc
      (2:ℝ) ≤ q^1 := by simpa only [pow_one] using hq
      _ ≤ q^x := pow_le_pow_right₀ hq1 (by omega)
  have hscale : C*q^J ≤ C*q^a := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 ha) hC.le
  have hsq : (C*q^J)^2 ≤ (C*q^a)^2 := by
    have : 0 ≤ C*q^J := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) (add_nonneg this (this.trans hscale))]
  have hwidth' : q^h * q^k ≤ (C*q^a)^2 := by
    rw [← pow_add]
    exact (pow_le_pow_right₀ hq1 hsum).trans (hwidth.trans hsq)
  apply no_cube_of_fits (hstart.trans hscale) (hp h hh) (hp k hk) (hp l hl)
    (herror.trans hsq) hwidth' (fits_rectangle hfit box)
  simpa only [pow_add, mul_assoc] using fits_rectangle hfit box'

end ArctanPole
