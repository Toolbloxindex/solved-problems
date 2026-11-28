module

public import InertBlock
public import MollRigidity
public import TangentBlocks

@[expose] public section

namespace ArctanPole
open MollRigidity Finset Real

private theorem gauss_step (n : ℕ) :
    gaussProd (n+1) = gaussProd n * ⟨1, ((n+1:ℕ):ℤ)⟩ :=
  prod_Icc_succ_top (by omega) _

/-- The squared modulus of the product is the product of the squared moduli. -/
theorem normBlock_coordinates (n : ℕ) :
    (normBlock n : ℤ) = (gaussProd n).re^2 + (gaussProd n).im^2 := by
  induction n with
  | zero => simp [normBlock, gaussProd]
  | succ n ih =>
    simp [normBlock,gauss_step,Zsqrtd.re_mul,Zsqrtd.im_mul, ih]
    ring

theorem factorial_sq_le_normBlock (n : ℕ) : n.factorial^2 ≤ normBlock n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [normBlock, Nat.factorial_succ, mul_pow, Nat.mul_comm]
    exact Nat.mul_le_mul ih (by omega)

/-- At any integer slope, the real coordinate is nonzero and the norm gives the height
identity with the literal coordinate gcd. -/
theorem normBlock_integer_slope {n : ℕ} {m : ℤ} (hm : (gaussProd n).im = (gaussProd n).re*m) :
    (gaussProd n).re ≠ 0 ∧
    normBlock n = (Int.gcd (gaussProd n).re (gaussProd n).im)^2 * (1+m.natAbs^2) := by
  have h := normBlock_coordinates n
  rw [hm] at h
  constructor
  · intro hz
    rw [hz] at h
    have hn := factorial_sq_le_normBlock n
    have hp := Nat.factorial_pos n
    simp at h
    rw [h] at hn
    simp_all
  · rw [Int.gcd_eq_natAbs_left ⟨m,hm⟩]
    apply Nat.cast_injective (R:=ℤ)
    push_cast
    simp only [sq_abs, h]
    ring

private theorem aligned (n : ℕ) :
    ((gaussProd n).im:ℝ)*cos (angle n) = ((gaussProd n).re:ℝ)*sin (angle n) := by
  induction n with
  | zero => simp [gaussProd, angle]
  | succ n ih =>
    let x : ℝ := n+1
    have hc := (cos_arctan_pos x).ne'
    have hs : sin (arctan x) = x * cos (arctan x) := by
      exact (div_eq_iff hc).mp ((tan_eq_sin_div_cos _).symm.trans (tan_arctan x))
    have ha : angle (n+1) = angle n + arctan x := by simp [angle, x, sum_range_succ]
    rw [gauss_step, ha, cos_add, sin_add, hs]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    push_cast
    dsimp [x] at *
    linear_combination (1+((n:ℝ)+1)^2) * cos (arctan ((n:ℝ)+1)) * ih

/-- A divisibility witness gives the actual tangent of the original sum. -/
theorem tangent_of_integer_slope {n : ℕ} {m : ℤ}
    (hm : (gaussProd n).im = (gaussProd n).re*m) : tan (angle n) = (m : ℝ) := by
  have h := aligned n
  rw [hm, Int.cast_mul] at h
  have hA : ((gaussProd n).re : ℝ) ≠ 0 := by exact_mod_cast (normBlock_integer_slope hm).1
  rw [mul_assoc] at h
  have hr := mul_left_cancel₀ hA h
  have hc : cos (angle n) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hr
    have hsc := sin_sq_add_cos_sq (angle n)
    rw [hz,←hr] at hsc
    norm_num at hsc
  exact (tan_eq_sin_div_cos _).trans ((div_eq_iff hc).mpr hr.symm)

#print axioms normBlock_integer_slope
#print axioms tangent_of_integer_slope

end ArctanPole
