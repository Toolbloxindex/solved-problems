import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace JacobiDiagonalControls

noncomputable def f2 (u x : ℝ) : ℝ :=
  (1 + u)^2 + (14 + 10*u)*x + (21 - 6*u - 3*u^2)*x^2 + 2*(2-u)*(1-u)*x^3

noncomputable def cubicDisc (a b c d : ℝ) : ℝ :=
  b^2*c^2 - 4*a*c^3 - 4*b^3*d - 27*a^2*d^2 + 18*a*b*c*d

/-- The cubic discriminant of the second diagonal numerator after removing its factor x. -/
noncomputable def disc (u : ℝ) : ℝ :=
  let a := 2*(2-u)*(1-u)
  let b := 21 - 6*u - 3*u^2
  let c := 14 + 10*u
  let d := (1+u)^2
  cubicDisc a b c d

theorem disc_pos_shift (s : ℝ) :
    disc (2+s) = 11376-198368*s-274352*s^2-164928*s^3-53744*s^4-9440*s^5-720*s^6 := by
  unfold disc cubicDisc
  ring

theorem disc_neg_shift (s : ℝ) :
    disc (-1-s) = 6144-25600*s-18176*s^2-19200*s^3-9344*s^4-3520*s^5-720*s^6 := by
  unfold disc cubicDisc
  ring

theorem f2_at_two (x : ℝ) : f2 2 x = 9 + 34*x - 3*x^2 := by
  unfold f2
  ring

theorem f2_at_three_pos {x : ℝ} (hx : 0 ≤ x) : 0 < f2 3 x := by
  have h : f2 3 x = 4*(x*(x-3)^2+2*x+4) := by unfold f2; ring
  rw [h]
  positivity

theorem disc_positive_cut_bracket : 0 < disc (41/20) ∧ disc (33/16) < 0 := by
  norm_num [disc, cubicDisc]

theorem disc_negative_cut_bracket : 0 < disc (-(6/5)) ∧ disc (-(121/100)) < 0 := by
  norm_num [disc, cubicDisc]

theorem f2_at_three_disc : disc 3 = -690176 := by
  norm_num [disc, cubicDisc]

theorem signed_sample :
    f2 (-(6/5)) (-2) < 0 ∧ 0 < f2 (-(6/5)) (-1) ∧
    f2 (-(6/5)) (-(1/20)) < 0 ∧ 0 < f2 (-(6/5)) 0 := by
  norm_num [f2]

private noncomputable def weight (u : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) + u)

/-- The source entries J(n+k,n;u), reindexed by rank k and column n. -/
noncomputable def diagonal (u : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | k+1 => Nat.rec 0 (fun n residue => residue + weight u (n+1) * diagonal u k (n+1))

private noncomputable def diagonalOne (u n : ℝ) : ℝ :=
  n * (n+1) * (2*n+1+3*u) / 6

private theorem diagonal_one (u : ℝ) (n : ℕ) :
    diagonal u 1 n = diagonalOne u n := by
  induction n with
  | zero => norm_num [diagonal, diagonalOne]
  | succ n ih =>
    change diagonal u 1 n + weight u (n+1) * 1 = _
    rw [mul_one, ih]
    simp only [weight, Nat.cast_succ]
    unfold diagonalOne
    ring

private noncomputable def chooseSix (n : ℝ) : ℝ :=
  n * (n-1) * (n-2) * (n-3) * (n-4) * (n-5) / 720

/-- Falling-factorial form for the n-th coefficient of x F₂(x;u) / (1-x)⁷. -/
noncomputable def secondSeriesCoeff (u n : ℝ) : ℝ :=
  (1+u)^2 * chooseSix (n+5) + (14+10*u) * chooseSix (n+4) +
    (21-6*u-3*u^2) * chooseSix (n+3) + 2*(2-u)*(1-u) * chooseSix (n+2)

theorem diagonal_two (u : ℝ) (n : ℕ) :
    diagonal u 2 n = secondSeriesCoeff u n := by
  induction n with
  | zero => norm_num [diagonal, secondSeriesCoeff, chooseSix]
  | succ n ih =>
    change diagonal u 2 n + weight u (n+1) * diagonal u 1 (n+1) = _
    rw [ih, diagonal_one]
    simp only [weight, Nat.cast_succ]
    unfold diagonalOne secondSeriesCoeff chooseSix
    ring

/-- If r is a root, division by x-r leaves the quadratic with coefficients a, B, C. -/
theorem cubic_at_root_factored {a b c d r : ℝ} (h : a*r^3+b*r^2+c*r+d=0)
    (x : ℝ) :
    a*x^3+b*x^2+c*x+d = (x-r)*(a*x^2+(b+a*r)*x+(c+b*r+a*r^2)) := by
  have hd : d = -(a*r^3+b*r^2+c*r) := by linarith
  rw [hd]
  ring

theorem cubic_disc_at_root {a b c d r : ℝ} (h : a*r^3+b*r^2+c*r+d=0) :
    cubicDisc a b c d =
      ((b+a*r)^2-4*a*(c+b*r+a*r^2))*(a*r^2+(b+a*r)*r+(c+b*r+a*r^2))^2 := by
  have hd : d = -(a*r^3+b*r^2+c*r) := by linarith
  rw [hd]
  unfold cubicDisc
  ring

theorem cubic_disc_criterion_at_root {a b c d r : ℝ} (h : a*r^3+b*r^2+c*r+d=0) :
    0 ≤ cubicDisc a b c d ↔ 0 ≤ (b+a*r)^2-4*a*(c+b*r+a*r^2) := by
  rw [cubic_disc_at_root h]
  constructor
  · intro hh
    by_cases hq : a*r^2+(b+a*r)*r+(c+b*r+a*r^2) = 0
    · have he : (b+a*r)^2-4*a*(c+b*r+a*r^2) = (2*a*r+(b+a*r))^2 := by
        calc
          _ = (2*a*r+(b+a*r))^2 -
                4*a*(a*r^2+(b+a*r)*r+(c+b*r+a*r^2)) := by ring
          _ = _ := by rw [hq, mul_zero, sub_zero]
      rw [he]
      positivity
    · by_contra! hneg
      exact (not_lt_of_ge hh) (mul_neg_of_neg_of_pos hneg (sq_pos_of_ne_zero hq))
  · intro hh
    exact mul_nonneg hh (sq_nonneg _)

end JacobiDiagonalControls
