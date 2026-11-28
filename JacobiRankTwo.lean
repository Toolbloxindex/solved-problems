module

public import JacobiDiscriminantInterval
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace JacobiRankTwo

open JacobiDiagonalControls JacobiDiscriminantInterval Set

private theorem monic_cubic_has_root (b c d : ℝ) :
    ∃ r : ℝ, r^3 + b*r^2 + c*r + d = 0 := by
  let R := 1 + |b| + |c| + |d|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg b, abs_nonneg c, abs_nonneg d]
  have hR0 : 0 ≤ R := by linarith
  have hR2 : 1 ≤ R^2 := by nlinarith
  have hRr : R ≤ R^2 := by nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hR)]
  have hB : |b*R^2| ≤ |b| *R^2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg R)]
  have hC : |c*R| ≤ |c| *R^2 := by
    rw [abs_mul, abs_of_nonneg hR0]
    exact mul_le_mul_of_nonneg_left hRr (abs_nonneg c)
  have hD : |d| ≤ |d| *R^2 := by
    simpa using mul_le_mul_of_nonneg_left hR2 (abs_nonneg d)
  have hs : (|b|+|c|+|d|)*R^2 < R^3 := by
    have he : |b|+|c|+|d| = R-1 := by dsimp [R]; ring
    rw [he]
    nlinarith [sq_pos_of_ne_zero (ne_of_gt (show R > 0 by linarith))]
  have negAbs (x : ℝ) : -(|x|) ≤ x := (abs_le.mp (le_rfl : |x| ≤ |x|)).1
  have hlo : (-R)^3 + b*(-R)^2 + c*(-R) + d ≤ 0 := by
    nlinarith [le_abs_self (b*R^2), negAbs (c*R), le_abs_self d]
  have hhi : 0 ≤ R^3 + b*R^2 + c*R + d := by
    nlinarith [negAbs (b*R^2), negAbs (c*R), negAbs d]
  let f : ℝ → ℝ := fun x => x^3 + b*x^2+c*x+d
  have hf : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc (show -R ≤ R by linarith)
    hf.continuousOn (show (0 : ℝ) ∈ Icc (f (-R)) (f R) from ⟨hlo,hhi⟩)
  exact ⟨r, hr⟩

private theorem cubic_has_root {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) :
    ∃ r : ℝ, a*r^3+b*r^2+c*r+d=0 := by
  obtain ⟨r,hr⟩ := monic_cubic_has_root (b/a) (c/a) (d/a)
  exact ⟨r, by
    field_simp [ha] at hr
    linear_combination hr⟩

private theorem quadratic_factors {a : ℝ} (ha : a ≠ 0) {b c : ℝ}
    (h : 0 ≤ b^2-4*a*c) :
    ∃ s t : ℝ, ∀ x : ℝ, a*x^2+b*x+c = a*(x-s)*(x-t) := by
  let z := Real.sqrt (b^2-4*a*c)
  have hz : z^2 = b^2-4*a*c := Real.sq_sqrt h
  refine ⟨(-b+z)/(2*a), (-b-z)/(2*a), fun x => ?_⟩
  field_simp [ha]
  linear_combination hz

/-- A nondegenerate real cubic splits into three real linear factors iff its discriminant
is nonnegative. The factors may repeat. -/
theorem cubic_factors_iff {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) :
    (∃ r s t : ℝ, ∀ x : ℝ, a*x^3+b*x^2+c*x+d = a*(x-r)*(x-s)*(x-t)) ↔
      0 ≤ cubicDisc a b c d := by
  constructor
  · rintro ⟨r,s,t,h⟩
    have h0 := h 0
    have h1 := h 1
    have hm := h (-1)
    have hd : d = -a*r*s*t := by linear_combination h0
    have hb : b = -a*(r+s+t) := by linear_combination (h1+hm)/2-h0
    have hc : c = a*(r*s+r*t+s*t) := by linear_combination (h1-hm)/2
    rw [hb,hc,hd]
    have id : cubicDisc a (-a*(r+s+t)) (a*(r*s+r*t+s*t)) (-a*r*s*t) =
        a^4*(r-s)^2*(r-t)^2*(s-t)^2 := by unfold cubicDisc; ring
    rw [id]
    positivity
  · intro h
    obtain ⟨r,hr⟩ := cubic_has_root ha b c d
    have hq := (cubic_disc_criterion_at_root hr).mp h
    obtain ⟨s,t,hs⟩ := quadratic_factors ha hq
    refine ⟨r,s,t,fun x => ?_⟩
    rw [cubic_at_root_factored hr x, hs x]
    ring

/-- The endpoint equations and strict outer monotonicity determine a single discriminant
interval. The rational endpoint brackets resolve the quadratic degree drops at 1 and 2. -/
theorem disc_interval :
    ∃ left ∈ Ioo (-(121/100) : ℝ) (-(6/5)),
      ∃ right ∈ Ioo (41/20 : ℝ) (33/16),
        disc left = 0 ∧ disc right = 0 ∧
          ∀ u : ℝ, 0 ≤ disc u ↔ left ≤ u ∧ u ≤ right := by
  let l₀ : ℝ := -(121/100)
  let l₁ : ℝ := -(6/5)
  let r₀ : ℝ := 41/20
  let r₁ : ℝ := 33/16
  have hc : Continuous disc := by unfold disc cubicDisc; fun_prop
  obtain ⟨left, ⟨hll, hlr⟩, hl⟩ := intermediate_value_Icc
    (show l₀ ≤ l₁ by norm_num [l₀, l₁]) hc.continuousOn
    (show (0 : ℝ) ∈ Icc (disc l₀) (disc l₁) from
      ⟨disc_negative_cut_bracket.2.le, disc_negative_cut_bracket.1.le⟩)
  obtain ⟨right, ⟨hrl, hrr⟩, hr⟩ := intermediate_value_Icc'
    (show r₀ ≤ r₁ by norm_num [r₀, r₁]) hc.continuousOn
    (show (0 : ℝ) ∈ Icc (disc r₁) (disc r₀) from
      ⟨disc_positive_cut_bracket.2.le, disc_positive_cut_bracket.1.le⟩)
  have hall : l₀ < left ∧ left < l₁ := by
    refine ⟨lt_of_le_of_ne hll ?_, lt_of_le_of_ne hlr ?_⟩
    · intro h
      rw [← h] at hl
      exact (ne_of_lt disc_negative_cut_bracket.2) hl
    · intro h
      rw [h] at hl
      exact (ne_of_gt disc_negative_cut_bracket.1) hl
  have harr : r₀ < right ∧ right < r₁ := by
    refine ⟨lt_of_le_of_ne hrl ?_, lt_of_le_of_ne hrr ?_⟩
    · intro h
      rw [← h] at hr
      exact (ne_of_gt disc_positive_cut_bracket.1) hr
    · intro h
      rw [h] at hr
      exact (ne_of_lt disc_positive_cut_bracket.2) hr
  refine ⟨left, hall, right, harr, hl, hr, disc_nonneg_iff_between ?_ ?_ hl hr⟩
  · dsimp [l₁] at hlr
    linarith
  · dsimp [r₀] at hrl
    linarith

/-- The rank-two numerator's real factorization, including both quadratic parameters.
The removed factor of x contributes one additional real zero. -/
def factors (u : ℝ) : Prop :=
  let a := 2*(2-u)*(1-u)
  let b := 21-6*u-3*u^2
  if a = 0 then
    ∃ r s : ℝ, ∀ x : ℝ, f2 u x = b*(x-r)*(x-s)
  else
    ∃ r s t : ℝ, ∀ x : ℝ, f2 u x = a*(x-r)*(x-s)*(x-t)

private theorem f2_at_one (x : ℝ) : f2 1 x = 4+24*x+12*x^2 := by
  unfold f2
  ring

theorem factors_iff_disc (u : ℝ) : factors u ↔ 0 ≤ disc u := by
  unfold factors
  dsimp only
  split
  · rename_i ha
    have hu : u = 2 ∨ u = 1 := by
      rcases mul_eq_zero.mp ha with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hu with rfl | rfl
    · have hd : 0 ≤ disc 2 := le_of_lt (disc_mid_pos (by norm_num) le_rfl)
      refine iff_of_true ?_ hd
      obtain ⟨r,s,hr⟩ := quadratic_factors (a := -3) (b := 34) (c := 9)
        (by norm_num) (by norm_num)
      exact ⟨r,s, fun x => by rw [f2_at_two]; linear_combination hr x⟩
    · have hd : 0 ≤ disc 1 := le_of_lt (disc_mid_pos (by norm_num) (by norm_num))
      refine iff_of_true ?_ hd
      obtain ⟨r,s,hr⟩ := quadratic_factors (a := 12) (b := 24) (c := 4)
        (by norm_num) (by norm_num)
      exact ⟨r,s, fun x => by rw [f2_at_one]; linear_combination hr x⟩
  · rename_i ha
    have h := cubic_factors_iff ha (21-6*u-3*u^2) (14+10*u) ((1+u)^2)
    have hx (x : ℝ) : f2 u x =
        (2*(2-u)*(1-u))*x^3+(21-6*u-3*u^2)*x^2+(14+10*u)*x+(1+u)^2 := by
      unfold f2
      ring
    simpa only [hx, disc] using h

theorem rank_two_sharp :
    ∃ left ∈ Ioo (-(121/100) : ℝ) (-(6/5)),
      ∃ right ∈ Ioo (41/20 : ℝ) (33/16),
        disc left = 0 ∧ disc right = 0 ∧
          ∀ u : ℝ, factors u ↔ left ≤ u ∧ u ≤ right := by
  obtain ⟨l, hl, r, hr, hdl, hdr, h⟩ := disc_interval
  exact ⟨l, hl, r, hr, hdl, hdr, fun u => (factors_iff_disc u).trans (h u)⟩

end JacobiRankTwo
