import MidpointPhase
import PoleCube

namespace ArctanPole
open Real

private theorem inverse_scaled {s w : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1/100)
    (hw : |w - 5/24*s + 19/192*s^2| ≤ 400*s^3) :
    |2*exp w - 5/12*s*exp (-w) + 13/192*s^2*exp (-3*w) - 2| ≤ 820*s^3 := by
  have hss := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs')
  have hss' := mul_nonneg hs (sub_nonneg.mpr hs')
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hw
  have hb : |w - 5/24*s| ≤ 5*s^2 := by apply abs_le.mpr; constructor <;> linarith
  obtain ⟨hb₁,hb₂⟩ := abs_le.mp hb
  have hw' : |w| ≤ s := by apply abs_le.mpr; constructor <;> linarith
  have hw1 : |w| ≤ 1 := by linarith
  have hs2 : |w|^2 ≤ s^2 := pow_le_pow_left₀ (abs_nonneg w) hw' 2
  have hs3 : |w|^3 ≤ s^3 := pow_le_pow_left₀ (abs_nonneg w) hw' 3
  have hx₃ := Real.exp_bound (n:=3) hw1 (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hx₃
  have h₃ : |exp w - (1+w+w^2/2)| ≤ s^3 := by
    exact le_trans hx₃ (show |w|^3 * (2/9:ℝ) ≤ s^3 by linarith [pow_nonneg (abs_nonneg w) 3])
  have h₂ := Real.abs_exp_sub_one_sub_id_le (x := -w) (by rwa [abs_neg])
  rw [neg_sq] at h₂
  rw [sq_abs] at hs2
  have h₁ := Real.abs_exp_sub_one_le (x := -3*w) (by rw [abs_mul]; norm_num; linarith)
  rw [abs_mul] at h₁
  norm_num at h₁
  rw [show -(3*w) = -3*w by ring] at h₁
  have hfac : |w^2 - (5/24*s)^2| ≤ 10*s^3 := by
    rw [sq_sub_sq, abs_mul]
    have hp : |w + 5/24*s| ≤ 2*s := by
      obtain ⟨hw₁,hw₂⟩ := abs_le.mp hw'
      apply abs_le.mpr; constructor <;> linarith
    calc
      _ ≤ (2*s)*(5*s^2) := mul_le_mul hp hb (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he₂ : |s*(exp (-w)-1-(-w))| ≤ s^3 := by
    rw [abs_mul, abs_of_nonneg hs]
    calc
      _ ≤ s*s^2 := mul_le_mul_of_nonneg_left (h₂.trans hs2) hs
      _ = _ := by ring
  have he₁ : |s^2*(exp (-3*w)-1)| ≤ 6*s^3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    calc
      _ ≤ s^2*(6*s) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg s)
      _ = _ := by ring
  have he_b : |s*(w-5/24*s)| ≤ 5*s^3 := by
    rw [abs_mul, abs_of_nonneg hs]
    calc
      _ ≤ s*(5*s^2) := mul_le_mul_of_nonneg_left hb hs
      _ = _ := by ring
  obtain ⟨hf₁,hf₂⟩ := abs_le.mp hfac
  obtain ⟨hc₁,hc₂⟩ := abs_le.mp h₃
  obtain ⟨ha₁,ha₂⟩ := abs_le.mp he₂
  obtain ⟨he₃,he₄⟩ := abs_le.mp he₁
  obtain ⟨hi₁,hi₂⟩ := abs_le.mp he_b
  apply abs_le.mpr
  constructor
  · linarith only [hd₁,hf₁,hc₁,ha₂,he₃,hi₁,pow_nonneg hs 3]
  · linarith only [hd₂,hf₂,hc₂,ha₁,he₄,hi₂,pow_nonneg hs 3]

private theorem scale_to_fits {z w t : ℝ} {y : ℤ}
    (hz : 0 < z) (ht : t=z*exp w) (hy : (y:ℝ)=2*z)
    (hs : 1/z^2 ≤ 1/100)
    (hw : |w - 5/24*(1/z^2) + 19/192*(1/z^2)^2| ≤ 400*(1/z^2)^3) :
    Fits 200000 t y := by
  let s := 1/z^2
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1/100 := hs
  have hd := abs_le.mp hw
  change -_ ≤ w-5/24*s+19/192*s^2 ∧ w-5/24*s+19/192*s^2 ≤ _ at hd
  have hw1 : |w| ≤ 1 := by
    apply abs_le.mpr
    have h₁ := mul_nonneg hs0 (sub_nonneg.mpr hs1)
    have h₂ := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1)
    obtain ⟨h₃,h₄⟩ := hd
    constructor <;> linarith
  have hexp : exp w ≤ 3 := by
    have h := (abs_le.mp (Real.abs_exp_sub_one_le hw1)).2
    linarith
  have ht0 : 0 < t := by rw [ht]; positivity
  have hpow : t^5 ≤ (3*z)^5 := pow_le_pow_left₀ ht0.le (by rw [ht]; nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hexp)]) 5
  have hi := inverse_scaled (s:=s) hs0 hs1 hw
  have heq : (2*t - 5/(12*t) + 13/(192*t^3) - 2*z)/z =
      2*exp w - 5/12*s*exp (-w) + 13/192*s^2*exp (-3*w) - 2 := by
    rw [show -3*w = -(3*w) by ring, Real.exp_neg, Real.exp_neg,
      show (3:ℝ)*w = w+w+w by ring, Real.exp_add, Real.exp_add, ht]
    dsimp [s]
    field_simp
  rw [←heq, abs_div, abs_of_pos hz, div_le_iff₀ hz] at hi
  change |2*t - 5/(12*t) + 13/(192*t^3) - 2*z| ≤ 820*(1/z^2)^3*z at hi
  have hi' : |2*t - 5/(12*t) + 13/(192*t^3) - 2*z| ≤ 820/z^5 := by
    apply hi.trans
    apply le_of_eq
    field_simp
  use ((y:ℝ) - (2*t - 5/(12*t) + 13/(192*t^3)))*t^5
  constructor
  · rw [abs_mul, abs_of_pos (pow_pos ht0 _), hy, abs_sub_comm]
    apply le_trans (mul_le_mul hi' hpow (pow_pos ht0 _).le (by positivity))
    field_simp
    nlinarith [pow_pos hz 5]
  · field_simp
    ring

/-- Every pole within n⁻⁶ of the actual reciprocal arctangent sum supplies an integer
observation for the finite determinant theorem. The same scale works at all such poles. -/
theorem phase_pole_fits :
    ∃ C : ℝ, ∀ (n : ℕ) (p : ℝ), 10 ≤ n → |phase n-p| ≤ 1/(n:ℝ)^6 →
      Fits 200000 (exp (p-C)) (2*(n:ℤ)+1) := by
  obtain ⟨C,hC⟩ := phase_midpoint
  refine ⟨C,fun n p hn hnear => ?_⟩
  let z : ℝ := (n:ℝ)+1/2
  let w : ℝ := p-C-log z
  have hn' : 10 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hs : 1/z^2 ≤ 1/100 := by
    rw [div_le_iff₀ (pow_pos hz _)]
    dsimp [z]; nlinarith [mul_nonneg (sub_nonneg.mpr hn') (by positivity : 0 ≤ (n:ℝ)+10)]
  have hcomp : 33/(n:ℝ)^6 ≤ 400*(1/z^2)^3 := by
    have h₁ : z ≤ 3/2*(n:ℝ) := by dsimp [z]; linarith
    have h₂ := pow_le_pow_left₀ hz.le h₁ 6
    field_simp
    nlinarith [pow_pos hn0 6]
  apply scale_to_fits (z:=z) (w:=w) hz
  · dsimp [w]
    rw [Real.exp_sub (p-C) (log z), exp_log hz]
    field_simp
  · dsimp [z]; push_cast; ring
  · exact hs
  · obtain ⟨h₁,h₂⟩ := hC n (by omega)
    change 0 ≤ phase n-(C+midpoint z) at h₁
    change phase n-(C+midpoint z) ≤ 32/(n:ℝ)^6 at h₂
    obtain ⟨h₃,h₄⟩ := abs_le.mp hnear
    apply le_trans _ hcomp
    have hrewrite : w - 5/24*(1/z^2) + 19/192*(1/z^2)^2 = p - (C+midpoint z) := by
      unfold w midpoint
      field_simp
      ring
    rw [hrewrite]
    apply abs_le.mpr
    simp only [div_eq_mul_inv, one_mul] at h₂ h₃ h₄ ⊢
    have hp : 0 ≤ ((n:ℝ)^6)⁻¹ := by positivity
    constructor <;> linarith

#print axioms phase_pole_fits

end ArctanPole
