module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace ArctanPole
open Real Set Filter
open scoped Topology

noncomputable def err (s : ℝ) : ℝ :=
  arctan (2*s) - log (1+s) + log (1-s) -
    5/6 * ((s/(1+s))^2 - (s/(1-s))^2) +
    19/12 * ((s/(1+s))^4 - (s/(1-s))^4)

noncomputable def rate (s : ℝ) : ℝ :=
  -s^6 * (1510 + 1388*s^2 + 142*s^4) / (3*(1+4*s^2)*(1-s^2)^5)

theorem err_deriv {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1/2) :
    HasDerivAt err (rate s) s := by
  have hu : (1:ℝ)+s ≠ 0 := by linarith
  have hv : (1:ℝ)-s ≠ 0 := by linarith
  have hsq : 1 - s^2 ≠ 0 := by nlinarith [mul_nonneg hs (show 0 ≤ 1/2-s by linarith)]
  have one := hasDerivAt_const s (1:ℝ)
  have x := hasDerivAt_id' s
  have u := one.add x
  have v := one.sub x
  have t := x.const_mul 2
  have a := (hasDerivAt_arctan (2*s)).comp s t
  have ru := x.div u hu
  have rv := x.div v hv
  apply HasDerivAt.congr_deriv (((((a.sub (u.log hu)).add (v.log hv)).sub
    (((ru.pow 2).sub (rv.pow 2)).const_mul (5/6))).add
    (((ru.pow 4).sub (rv.pow 4)).const_mul (19/12))))
  dsimp [rate]
  field_simp [hu, hv, hsq]
  ring


end ArctanPole
