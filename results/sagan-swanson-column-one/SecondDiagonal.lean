import Std

/-! Strict parity Turán inequalities for the explicit coefficient formula on
the second type-B q-Stirling diagonal. The generating-function derivation
identifying the formula with the published polynomials is in the proof note. -/
namespace SecondDiagonal
set_option maxHeartbeats 2000000

def b3 (z : Int) := (z+1)*(z+2)
def b4 (z : Int) := (z+1)*(z+2)*(z+3)
def l4 (z s : Int) := (z+2-s)*(z+2+s)

def value (e odd hi : Bool) (m t s : Int) : Int :=
  let sign : Int := if e then -1 else 1
  let a := m+sign
  let b (z : Int) := if hi then b3 (z-m) else 0
  let c (z : Int) := if hi then b4 (z-m) else 0
  if odd then
    24*m*a*(t+1) - 12*a*(b3 t + b3 (t-1) - b t - b (t-1))
    + 4*(b4 (t-1) - 2*c (t-1)) + 6*sign*l4 (t-1) (1-s)
  else
    12*m*a*(2*t+1) - 24*a*(b3 (t-1) - b (t-1))
    + 2*(b4 (t-1) + b4 (t-2) - 2*c (t-1) - 2*c (t-2))
    + 3*sign*(l4 (t-1) (1-s) + l4 (t-2) s)

/-- 24 times the coefficient at degree 2*t+p in e₂ (e=true) or h₂ (e=false)
in the m variables [1],[3],...,[2*m-1], for degrees within its support. -/
def coeff24 (e odd : Bool) (m t : Int) : Int :=
  value e odd (decide (m ≤ t)) m t (t%2)

/-- Difference of the square and cross product for three successive terms
of the specified parity. -/
def gap (e odd : Bool) (m t : Int) : Int :=
  coeff24 e odd m (t+1) ^ 2 - coeff24 e odd m t * coeff24 e odd m (t+2)


private theorem cert_0_0_low_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false false (2*v+0+3+u) (2*v+0) := by
  let m : Int := 2*v+0+3+u
  let t : Int := 2*v+0
  change 0 < gap false false m t
  have h0 : coeff24 false false m t = value false false false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false false m (t+1) = value false false false m (t+1) 1 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false false m (t+2) = value false false false m (t+2) 0 := by
    have hc : ¬ m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false false m t = 576*(u^4 * v^0) + 2304*(u^3 * v^1) + 6336*(u^3 * v^0) + 4608*(u^2 * v^2) + 20160*(u^2 * v^1) + 25920*(u^2 * v^0) + 6144*(u^1 * v^3) + 32256*(u^1 * v^2) + 62400*(u^1 * v^1) + 47808*(u^1 * v^0) + 3840*(u^0 * v^4) + 25344*(u^0 * v^3) + 62400*(u^0 * v^2) + 71424*(u^0 * v^1) + 35136 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp4_0 : 0 ≤ (u^4 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_1 : 0 ≤ (u^3 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_0 : 0 ≤ (u^3 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_2 : 0 ≤ (u^2 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_1 : 0 ≤ (u^2 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_0 : 0 ≤ (u^2 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_3 : 0 ≤ (u^1 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_2 : 0 ≤ (u^1 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_1 : 0 ≤ (u^1 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_0 : 0 ≤ (u^1 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_0_cross2_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false false (2+2*v+0) (0+2*v+0) := by
  let m : Int := 2+2*v+0
  let t : Int := 0+2*v+0
  change 0 < gap false false m t
  have h0 : coeff24 false false m t = value false false false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false false m (t+1) = value false false false m (t+1) 1 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false false m (t+2) = value false false true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false false m t = 3840*(u^0 * v^4) + 19200*(u^0 * v^3) + 34752*(u^0 * v^2) + 26880*(u^0 * v^1) + 7488 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_0_cross1_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false false (3+2*v+0) (2+2*v+0) := by
  let m : Int := 3+2*v+0
  let t : Int := 2+2*v+0
  change 0 < gap false false m t
  have h0 : coeff24 false false m t = value false false false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false false m (t+1) = value false false true m (t+1) 1 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false false m (t+2) = value false false true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false false m t = 768*(u^0 * v^4) + 4608*(u^0 * v^3) + 10176*(u^0 * v^2) + 9792*(u^0 * v^1) + 3456 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_0_high_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false false (4+u+2*v+0) (4+2*u+2*v+0) := by
  let m : Int := 4+u+2*v+0
  let t : Int := 4+2*u+2*v+0
  change 0 < gap false false m t
  have h0 : coeff24 false false m t = value false false true m t 0 := by
    have hc : m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false false m (t+1) = value false false true m (t+1) 1 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false false m (t+2) = value false false true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false false m t = 768*(u^0 * v^4) + 4608*(u^0 * v^3) + 10176*(u^0 * v^2) + 9792*(u^0 * v^1) + 3456 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_0_low_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false false (2*v+1+3+u) (2*v+1) := by
  let m : Int := 2*v+1+3+u
  let t : Int := 2*v+1
  change 0 < gap false false m t
  have h0 : coeff24 false false m t = value false false false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false false m (t+1) = value false false false m (t+1) 0 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false false m (t+2) = value false false false m (t+2) 1 := by
    have hc : ¬ m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false false m t = 576*(u^4 * v^0) + 2304*(u^3 * v^1) + 7488*(u^3 * v^0) + 4608*(u^2 * v^2) + 24768*(u^2 * v^1) + 37152*(u^2 * v^0) + 6144*(u^1 * v^3) + 41472*(u^1 * v^2) + 99264*(u^1 * v^1) + 87840*(u^1 * v^0) + 3840*(u^0 * v^4) + 33024*(u^0 * v^3) + 106176*(u^0 * v^2) + 154752*(u^0 * v^1) + 89856 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp4_0 : 0 ≤ (u^4 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_1 : 0 ≤ (u^3 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_0 : 0 ≤ (u^3 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_2 : 0 ≤ (u^2 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_1 : 0 ≤ (u^2 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_0 : 0 ≤ (u^2 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_3 : 0 ≤ (u^1 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_2 : 0 ≤ (u^1 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_1 : 0 ≤ (u^1 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_0 : 0 ≤ (u^1 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_0_cross2_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false false (2+2*v+1) (0+2*v+1) := by
  let m : Int := 2+2*v+1
  let t : Int := 0+2*v+1
  change 0 < gap false false m t
  have h0 : coeff24 false false m t = value false false false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false false m (t+1) = value false false false m (t+1) 0 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false false m (t+2) = value false false true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false false m t = 3840*(u^0 * v^4) + 26880*(u^0 * v^3) + 69312*(u^0 * v^2) + 77952*(u^0 * v^1) + 32256 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_0_cross1_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false false (3+2*v+1) (2+2*v+1) := by
  let m : Int := 3+2*v+1
  let t : Int := 2+2*v+1
  change 0 < gap false false m t
  have h0 : coeff24 false false m t = value false false false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false false m (t+1) = value false false true m (t+1) 0 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false false m (t+2) = value false false true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false false m t = 768*(u^0 * v^4) + 6144*(u^0 * v^3) + 18240*(u^0 * v^2) + 23808*(u^0 * v^1) + 11520 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_0_high_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false false (4+u+2*v+1) (4+2*u+2*v+1) := by
  let m : Int := 4+u+2*v+1
  let t : Int := 4+2*u+2*v+1
  change 0 < gap false false m t
  have h0 : coeff24 false false m t = value false false true m t 1 := by
    have hc : m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false false m (t+1) = value false false true m (t+1) 0 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false false m (t+2) = value false false true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false false m t = 768*(u^0 * v^4) + 6144*(u^0 * v^3) + 18240*(u^0 * v^2) + 23808*(u^0 * v^1) + 11520 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_1_low_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false true (2*v+0+3+u) (2*v+0) := by
  let m : Int := 2*v+0+3+u
  let t : Int := 2*v+0
  change 0 < gap false true m t
  have h0 : coeff24 false true m t = value false true false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false true m (t+1) = value false true false m (t+1) 1 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false true m (t+2) = value false true false m (t+2) 0 := by
    have hc : ¬ m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false true m t = 576*(u^4 * v^0) + 2304*(u^3 * v^1) + 5760*(u^3 * v^0) + 4608*(u^2 * v^2) + 19584*(u^2 * v^1) + 21888*(u^2 * v^0) + 6144*(u^1 * v^3) + 33408*(u^1 * v^2) + 61824*(u^1 * v^1) + 39168*(u^1 * v^0) + 3840*(u^0 * v^4) + 26496*(u^0 * v^3) + 67584*(u^0 * v^2) + 74880*(u^0 * v^1) + 29952 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp4_0 : 0 ≤ (u^4 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_1 : 0 ≤ (u^3 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_0 : 0 ≤ (u^3 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_2 : 0 ≤ (u^2 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_1 : 0 ≤ (u^2 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_0 : 0 ≤ (u^2 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_3 : 0 ≤ (u^1 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_2 : 0 ≤ (u^1 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_1 : 0 ≤ (u^1 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_0 : 0 ≤ (u^1 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_1_cross2_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false true (3+2*v+0) (1+2*v+0) := by
  let m : Int := 3+2*v+0
  let t : Int := 1+2*v+0
  change 0 < gap false true m t
  have h0 : coeff24 false true m t = value false true false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false true m (t+1) = value false true false m (t+1) 0 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false true m (t+2) = value false true true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false true m t = 2304*(u^0 * v^4) + 13824*(u^0 * v^3) + 29952*(u^0 * v^2) + 27648*(u^0 * v^1) + 9216 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_1_cross1_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false true (4+2*v+0) (3+2*v+0) := by
  let m : Int := 4+2*v+0
  let t : Int := 3+2*v+0
  change 0 < gap false true m t
  have h0 : coeff24 false true m t = value false true false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false true m (t+1) = value false true true m (t+1) 0 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false true m (t+2) = value false true true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false true m t = 768*(u^0 * v^4) + 4992*(u^0 * v^3) + 11904*(u^0 * v^2) + 12288*(u^0 * v^1) + 4608 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_1_high_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false true (5+u+2*v+0) (5+2*u+2*v+0) := by
  let m : Int := 5+u+2*v+0
  let t : Int := 5+2*u+2*v+0
  change 0 < gap false true m t
  have h0 : coeff24 false true m t = value false true true m t 1 := by
    have hc : m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false true m (t+1) = value false true true m (t+1) 0 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false true m (t+2) = value false true true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false true m t = 768*(u^0 * v^4) + 4992*(u^0 * v^3) + 11904*(u^0 * v^2) + 12288*(u^0 * v^1) + 4608 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_1_low_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false true (2*v+1+3+u) (2*v+1) := by
  let m : Int := 2*v+1+3+u
  let t : Int := 2*v+1
  change 0 < gap false true m t
  have h0 : coeff24 false true m t = value false true false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false true m (t+1) = value false true false m (t+1) 0 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false true m (t+2) = value false true false m (t+2) 1 := by
    have hc : ¬ m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false true m t = 576*(u^4 * v^0) + 2304*(u^3 * v^1) + 6912*(u^3 * v^0) + 4608*(u^2 * v^2) + 23040*(u^2 * v^1) + 31104*(u^2 * v^0) + 6144*(u^1 * v^3) + 40320*(u^1 * v^2) + 89472*(u^1 * v^1) + 69120*(u^1 * v^0) + 3840*(u^0 * v^4) + 33408*(u^0 * v^3) + 106752*(u^0 * v^2) + 148608*(u^0 * v^1) + 76608 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp4_0 : 0 ≤ (u^4 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_1 : 0 ≤ (u^3 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_0 : 0 ≤ (u^3 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_2 : 0 ≤ (u^2 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_1 : 0 ≤ (u^2 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_0 : 0 ≤ (u^2 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_3 : 0 ≤ (u^1 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_2 : 0 ≤ (u^1 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_1 : 0 ≤ (u^1 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_0 : 0 ≤ (u^1 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_1_cross2_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false true (3+2*v+1) (1+2*v+1) := by
  let m : Int := 3+2*v+1
  let t : Int := 1+2*v+1
  change 0 < gap false true m t
  have h0 : coeff24 false true m t = value false true false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false true m (t+1) = value false true false m (t+1) 1 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false true m (t+2) = value false true true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false true m t = 2304*(u^0 * v^4) + 19200*(u^0 * v^3) + 59328*(u^0 * v^2) + 80448*(u^0 * v^1) + 40320 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_1_cross1_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false true (4+2*v+1) (3+2*v+1) := by
  let m : Int := 4+2*v+1
  let t : Int := 3+2*v+1
  change 0 < gap false true m t
  have h0 : coeff24 false true m t = value false true false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false true m (t+1) = value false true true m (t+1) 1 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false true m (t+2) = value false true true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false true m t = 768*(u^0 * v^4) + 7296*(u^0 * v^3) + 25728*(u^0 * v^2) + 39936*(u^0 * v^1) + 23040 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_0_1_high_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap false true (5+u+2*v+1) (5+2*u+2*v+1) := by
  let m : Int := 5+u+2*v+1
  let t : Int := 5+2*u+2*v+1
  change 0 < gap false true m t
  have h0 : coeff24 false true m t = value false true true m t 0 := by
    have hc : m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 false true m (t+1) = value false true true m (t+1) 1 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 false true m (t+2) = value false true true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap false true m t = 768*(u^0 * v^4) + 7296*(u^0 * v^3) + 25728*(u^0 * v^2) + 39936*(u^0 * v^1) + 23040 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_0_low_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true false (2*v+0+3+u) (2*v+0) := by
  let m : Int := 2*v+0+3+u
  let t : Int := 2*v+0
  change 0 < gap true false m t
  have h0 : coeff24 true false m t = value true false false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true false m (t+1) = value true false false m (t+1) 1 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true false m (t+2) = value true false false m (t+2) 0 := by
    have hc : ¬ m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true false m t = 576*(u^4 * v^0) + 2304*(u^3 * v^1) + 4032*(u^3 * v^0) + 4608*(u^2 * v^2) + 14400*(u^2 * v^1) + 11232*(u^2 * v^0) + 6144*(u^1 * v^3) + 23040*(u^1 * v^2) + 31296*(u^1 * v^1) + 14688*(u^1 * v^0) + 3840*(u^0 * v^4) + 16128*(u^0 * v^3) + 27840*(u^0 * v^2) + 23040*(u^0 * v^1) + 7488 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp4_0 : 0 ≤ (u^4 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_1 : 0 ≤ (u^3 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_0 : 0 ≤ (u^3 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_2 : 0 ≤ (u^2 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_1 : 0 ≤ (u^2 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_0 : 0 ≤ (u^2 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_3 : 0 ≤ (u^1 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_2 : 0 ≤ (u^1 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_1 : 0 ≤ (u^1 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_0 : 0 ≤ (u^1 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_0_cross2_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true false (3+2*v+0) (1+2*v+0) := by
  let m : Int := 3+2*v+0
  let t : Int := 1+2*v+0
  change 0 < gap true false m t
  have h0 : coeff24 true false m t = value true false false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true false m (t+1) = value true false false m (t+1) 0 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true false m (t+2) = value true false true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true false m t = 3840*(u^0 * v^4) + 17664*(u^0 * v^3) + 30144*(u^0 * v^2) + 22656*(u^0 * v^1) + 6336 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_0_cross1_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true false (4+2*v+0) (3+2*v+0) := by
  let m : Int := 4+2*v+0
  let t : Int := 3+2*v+0
  change 0 < gap true false m t
  have h0 : coeff24 true false m t = value true false false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true false m (t+1) = value true false true m (t+1) 0 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true false m (t+2) = value true false true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true false m t = 768*(u^0 * v^4) + 4608*(u^0 * v^3) + 10176*(u^0 * v^2) + 9792*(u^0 * v^1) + 3456 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_0_high_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true false (5+u+2*v+0) (5+2*u+2*v+0) := by
  let m : Int := 5+u+2*v+0
  let t : Int := 5+2*u+2*v+0
  change 0 < gap true false m t
  have h0 : coeff24 true false m t = value true false true m t 1 := by
    have hc : m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true false m (t+1) = value true false true m (t+1) 0 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true false m (t+2) = value true false true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true false m t = 768*(u^0 * v^4) + 4608*(u^0 * v^3) + 10176*(u^0 * v^2) + 9792*(u^0 * v^1) + 3456 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_0_low_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true false (2*v+1+3+u) (2*v+1) := by
  let m : Int := 2*v+1+3+u
  let t : Int := 2*v+1
  change 0 < gap true false m t
  have h0 : coeff24 true false m t = value true false false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true false m (t+1) = value true false false m (t+1) 0 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true false m (t+2) = value true false false m (t+2) 1 := by
    have hc : ¬ m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true false m t = 576*(u^4 * v^0) + 2304*(u^3 * v^1) + 5184*(u^3 * v^0) + 4608*(u^2 * v^2) + 19008*(u^2 * v^1) + 19584*(u^2 * v^0) + 6144*(u^1 * v^3) + 32256*(u^1 * v^2) + 58944*(u^1 * v^1) + 36864*(u^1 * v^0) + 3840*(u^0 * v^4) + 23808*(u^0 * v^3) + 57792*(u^0 * v^2) + 64896*(u^0 * v^1) + 28224 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp4_0 : 0 ≤ (u^4 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_1 : 0 ≤ (u^3 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_0 : 0 ≤ (u^3 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_2 : 0 ≤ (u^2 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_1 : 0 ≤ (u^2 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_0 : 0 ≤ (u^2 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_3 : 0 ≤ (u^1 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_2 : 0 ≤ (u^1 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_1 : 0 ≤ (u^1 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_0 : 0 ≤ (u^1 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_0_cross2_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true false (3+2*v+1) (1+2*v+1) := by
  let m : Int := 3+2*v+1
  let t : Int := 1+2*v+1
  change 0 < gap true false m t
  have h0 : coeff24 true false m t = value true false false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true false m (t+1) = value true false false m (t+1) 1 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true false m (t+2) = value true false true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true false m t = 3840*(u^0 * v^4) + 25344*(u^0 * v^3) + 62400*(u^0 * v^2) + 67968*(u^0 * v^1) + 27648 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_0_cross1_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true false (4+2*v+1) (3+2*v+1) := by
  let m : Int := 4+2*v+1
  let t : Int := 3+2*v+1
  change 0 < gap true false m t
  have h0 : coeff24 true false m t = value true false false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true false m (t+1) = value true false true m (t+1) 1 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true false m (t+2) = value true false true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true false m t = 768*(u^0 * v^4) + 6144*(u^0 * v^3) + 18240*(u^0 * v^2) + 23808*(u^0 * v^1) + 11520 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_0_high_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true false (5+u+2*v+1) (5+2*u+2*v+1) := by
  let m : Int := 5+u+2*v+1
  let t : Int := 5+2*u+2*v+1
  change 0 < gap true false m t
  have h0 : coeff24 true false m t = value true false true m t 0 := by
    have hc : m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true false m (t+1) = value true false true m (t+1) 1 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true false m (t+2) = value true false true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true false m t = 768*(u^0 * v^4) + 6144*(u^0 * v^3) + 18240*(u^0 * v^2) + 23808*(u^0 * v^1) + 11520 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_1_low_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true true (2*v+0+3+u) (2*v+0) := by
  let m : Int := 2*v+0+3+u
  let t : Int := 2*v+0
  change 0 < gap true true m t
  have h0 : coeff24 true true m t = value true true false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true true m (t+1) = value true true false m (t+1) 1 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true true m (t+2) = value true true false m (t+2) 0 := by
    have hc : ¬ m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true true m t = 576*(u^4 * v^0) + 2304*(u^3 * v^1) + 3456*(u^3 * v^0) + 4608*(u^2 * v^2) + 12672*(u^2 * v^1) + 8064*(u^2 * v^0) + 6144*(u^1 * v^3) + 21888*(u^1 * v^2) + 24960*(u^1 * v^1) + 9216*(u^1 * v^0) + 3840*(u^0 * v^4) + 16512*(u^0 * v^3) + 26112*(u^0 * v^2) + 18048*(u^0 * v^1) + 4608 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp4_0 : 0 ≤ (u^4 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_1 : 0 ≤ (u^3 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_0 : 0 ≤ (u^3 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_2 : 0 ≤ (u^2 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_1 : 0 ≤ (u^2 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_0 : 0 ≤ (u^2 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_3 : 0 ≤ (u^1 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_2 : 0 ≤ (u^1 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_1 : 0 ≤ (u^1 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_0 : 0 ≤ (u^1 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_1_cross2_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true true (4+2*v+0) (2+2*v+0) := by
  let m : Int := 4+2*v+0
  let t : Int := 2+2*v+0
  change 0 < gap true true m t
  have h0 : coeff24 true true m t = value true true false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true true m (t+1) = value true true false m (t+1) 1 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true true m (t+2) = value true true true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true true m t = 2304*(u^0 * v^4) + 13056*(u^0 * v^3) + 27072*(u^0 * v^2) + 24384*(u^0 * v^1) + 8064 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_1_cross1_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true true (5+2*v+0) (4+2*v+0) := by
  let m : Int := 5+2*v+0
  let t : Int := 4+2*v+0
  change 0 < gap true true m t
  have h0 : coeff24 true true m t = value true true false m t 0 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true true m (t+1) = value true true true m (t+1) 1 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true true m (t+2) = value true true true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true true m t = 768*(u^0 * v^4) + 4992*(u^0 * v^3) + 11904*(u^0 * v^2) + 12288*(u^0 * v^1) + 4608 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_1_high_0 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true true (6+u+2*v+0) (6+2*u+2*v+0) := by
  let m : Int := 6+u+2*v+0
  let t : Int := 6+2*u+2*v+0
  change 0 < gap true true m t
  have h0 : coeff24 true true m t = value true true true m t 0 := by
    have hc : m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true true m (t+1) = value true true true m (t+1) 1 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true true m (t+2) = value true true true m (t+2) 0 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true true m t = 768*(u^0 * v^4) + 4992*(u^0 * v^3) + 11904*(u^0 * v^2) + 12288*(u^0 * v^1) + 4608 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_1_low_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true true (2*v+1+3+u) (2*v+1) := by
  let m : Int := 2*v+1+3+u
  let t : Int := 2*v+1
  change 0 < gap true true m t
  have h0 : coeff24 true true m t = value true true false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true true m (t+1) = value true true false m (t+1) 0 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true true m (t+2) = value true true false m (t+2) 1 := by
    have hc : ¬ m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true true m t = 576*(u^4 * v^0) + 2304*(u^3 * v^1) + 4608*(u^3 * v^0) + 4608*(u^2 * v^2) + 18432*(u^2 * v^1) + 17280*(u^2 * v^0) + 6144*(u^1 * v^3) + 33408*(u^1 * v^2) + 59520*(u^1 * v^1) + 34560*(u^1 * v^0) + 3840*(u^0 * v^4) + 24960*(u^0 * v^3) + 61824*(u^0 * v^2) + 68352*(u^0 * v^1) + 28224 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp4_0 : 0 ≤ (u^4 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_1 : 0 ≤ (u^3 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp3_0 : 0 ≤ (u^3 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_2 : 0 ≤ (u^2 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_1 : 0 ≤ (u^2 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp2_0 : 0 ≤ (u^2 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_3 : 0 ≤ (u^1 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_2 : 0 ≤ (u^1 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_1 : 0 ≤ (u^1 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp1_0 : 0 ≤ (u^1 * v^0) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_1_cross2_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true true (4+2*v+1) (2+2*v+1) := by
  let m : Int := 4+2*v+1
  let t : Int := 2+2*v+1
  change 0 < gap true true m t
  have h0 : coeff24 true true m t = value true true false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true true m (t+1) = value true true false m (t+1) 0 := by
    have hc : ¬ m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true true m (t+2) = value true true true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true true m t = 2304*(u^0 * v^4) + 18432*(u^0 * v^3) + 55296*(u^0 * v^2) + 73728*(u^0 * v^1) + 36864 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_1_cross1_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true true (5+2*v+1) (4+2*v+1) := by
  let m : Int := 5+2*v+1
  let t : Int := 4+2*v+1
  change 0 < gap true true m t
  have h0 : coeff24 true true m t = value true true false m t 1 := by
    have hc : ¬ m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true true m (t+1) = value true true true m (t+1) 0 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true true m (t+2) = value true true true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true true m t = 768*(u^0 * v^4) + 7296*(u^0 * v^3) + 25728*(u^0 * v^2) + 39936*(u^0 * v^1) + 23040 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cert_1_1_high_1 (u v : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < gap true true (6+u+2*v+1) (6+2*u+2*v+1) := by
  let m : Int := 6+u+2*v+1
  let t : Int := 6+2*u+2*v+1
  change 0 < gap true true m t
  have h0 : coeff24 true true m t = value true true true m t 1 := by
    have hc : m ≤ t := by dsimp [m,t]; omega
    have hr : t%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h1 : coeff24 true true m (t+1) = value true true true m (t+1) 0 := by
    have hc : m ≤ (t+1) := by dsimp [m,t]; omega
    have hr : (t+1)%2 = 0 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have h2 : coeff24 true true m (t+2) = value true true true m (t+2) 1 := by
    have hc : m ≤ (t+2) := by dsimp [m,t]; omega
    have hr : (t+2)%2 = 1 := by dsimp [t]; omega
    simp [coeff24, hc, hr]
  have id : gap true true m t = 768*(u^0 * v^4) + 7296*(u^0 * v^3) + 25728*(u^0 * v^2) + 39936*(u^0 * v^1) + 23040 := by
    unfold gap
    rw [h0,h1,h2]
    dsimp [value,b3,b4,l4,m,t]
    grind only
  rw [id]
  have hp0_4 : 0 ≤ (u^0 * v^4) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_3 : 0 ≤ (u^0 * v^3) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_2 : 0 ≤ (u^0 * v^2) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  have hp0_1 : 0 ≤ (u^0 * v^1) := Int.mul_nonneg (Int.pow_nonneg hu) (Int.pow_nonneg hv)
  omega

private theorem cover00 (m t : Int) (ht : 0 ≤ t) (hs : t ≤ 2*m-4) :
    0 < gap false false m t := by
  by_cases hlow : t ≤ m-3
  · let u : Int := m-3-t
    let v : Int := (t)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (t) % 2 = 0
    · have h := cert_0_0_low_0 u v hu hv
      have hm : 2*v+0+3+u = m := by dsimp [u,v] at *; omega
      have ht2 : 2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_0_0_low_1 u v hu hv
      have hm : 2*v+1+3+u = m := by dsimp [u,v] at *; omega
      have ht2 : 2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  by_cases hcross2 : t = m-2
  · let u : Int := 0
    let v : Int := (m-2)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-2) % 2 = 0
    · have h := cert_0_0_cross2_0 u v hu hv
      have hm : 2+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 0+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_0_0_cross2_1 u v hu hv
      have hm : 2+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 0+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  by_cases hcross1 : t = m-1
  · let u : Int := 0
    let v : Int := (m-3)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-3) % 2 = 0
    · have h := cert_0_0_cross1_0 u v hu hv
      have hm : 3+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 2+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_0_0_cross1_1 u v hu hv
      have hm : 3+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 2+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  · let u : Int := t-m
    let v : Int := (m-4-u)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-4-u) % 2 = 0
    · have h := cert_0_0_high_0 u v hu hv
      have hm : 4+u+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 4+2*u+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_0_0_high_1 u v hu hv
      have hm : 4+u+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 4+2*u+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
private theorem cover01 (m t : Int) (ht : 0 ≤ t) (hs : t ≤ 2*m-5) :
    0 < gap false true m t := by
  by_cases hlow : t ≤ m-3
  · let u : Int := m-3-t
    let v : Int := (t)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (t) % 2 = 0
    · have h := cert_0_1_low_0 u v hu hv
      have hm : 2*v+0+3+u = m := by dsimp [u,v] at *; omega
      have ht2 : 2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_0_1_low_1 u v hu hv
      have hm : 2*v+1+3+u = m := by dsimp [u,v] at *; omega
      have ht2 : 2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  by_cases hcross2 : t = m-2
  · let u : Int := 0
    let v : Int := (m-3)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-3) % 2 = 0
    · have h := cert_0_1_cross2_0 u v hu hv
      have hm : 3+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 1+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_0_1_cross2_1 u v hu hv
      have hm : 3+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 1+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  by_cases hcross1 : t = m-1
  · let u : Int := 0
    let v : Int := (m-4)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-4) % 2 = 0
    · have h := cert_0_1_cross1_0 u v hu hv
      have hm : 4+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 3+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_0_1_cross1_1 u v hu hv
      have hm : 4+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 3+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  · let u : Int := t-m
    let v : Int := (m-5-u)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-5-u) % 2 = 0
    · have h := cert_0_1_high_0 u v hu hv
      have hm : 5+u+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 5+2*u+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_0_1_high_1 u v hu hv
      have hm : 5+u+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 5+2*u+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
private theorem cover10 (m t : Int) (ht : 0 ≤ t) (hs : t ≤ 2*m-5) :
    0 < gap true false m t := by
  by_cases hlow : t ≤ m-3
  · let u : Int := m-3-t
    let v : Int := (t)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (t) % 2 = 0
    · have h := cert_1_0_low_0 u v hu hv
      have hm : 2*v+0+3+u = m := by dsimp [u,v] at *; omega
      have ht2 : 2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_1_0_low_1 u v hu hv
      have hm : 2*v+1+3+u = m := by dsimp [u,v] at *; omega
      have ht2 : 2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  by_cases hcross2 : t = m-2
  · let u : Int := 0
    let v : Int := (m-3)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-3) % 2 = 0
    · have h := cert_1_0_cross2_0 u v hu hv
      have hm : 3+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 1+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_1_0_cross2_1 u v hu hv
      have hm : 3+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 1+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  by_cases hcross1 : t = m-1
  · let u : Int := 0
    let v : Int := (m-4)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-4) % 2 = 0
    · have h := cert_1_0_cross1_0 u v hu hv
      have hm : 4+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 3+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_1_0_cross1_1 u v hu hv
      have hm : 4+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 3+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  · let u : Int := t-m
    let v : Int := (m-5-u)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-5-u) % 2 = 0
    · have h := cert_1_0_high_0 u v hu hv
      have hm : 5+u+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 5+2*u+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_1_0_high_1 u v hu hv
      have hm : 5+u+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 5+2*u+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
private theorem cover11 (m t : Int) (ht : 0 ≤ t) (hs : t ≤ 2*m-6) :
    0 < gap true true m t := by
  by_cases hlow : t ≤ m-3
  · let u : Int := m-3-t
    let v : Int := (t)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (t) % 2 = 0
    · have h := cert_1_1_low_0 u v hu hv
      have hm : 2*v+0+3+u = m := by dsimp [u,v] at *; omega
      have ht2 : 2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_1_1_low_1 u v hu hv
      have hm : 2*v+1+3+u = m := by dsimp [u,v] at *; omega
      have ht2 : 2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  by_cases hcross2 : t = m-2
  · let u : Int := 0
    let v : Int := (m-4)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-4) % 2 = 0
    · have h := cert_1_1_cross2_0 u v hu hv
      have hm : 4+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 2+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_1_1_cross2_1 u v hu hv
      have hm : 4+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 2+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  by_cases hcross1 : t = m-1
  · let u : Int := 0
    let v : Int := (m-5)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-5) % 2 = 0
    · have h := cert_1_1_cross1_0 u v hu hv
      have hm : 5+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 4+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_1_1_cross1_1 u v hu hv
      have hm : 5+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 4+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
  · let u : Int := t-m
    let v : Int := (m-6-u)/2
    have hu : 0 ≤ u := by dsimp [u]; omega
    have hv : 0 ≤ v := by dsimp [v,u]; omega
    by_cases hr : (m-6-u) % 2 = 0
    · have h := cert_1_1_high_0 u v hu hv
      have hm : 6+u+2*v+0 = m := by dsimp [u,v] at *; omega
      have ht2 : 6+2*u+2*v+0 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
    · have h := cert_1_1_high_1 u v hu hv
      have hm : 6+u+2*v+1 = m := by dsimp [u,v] at *; omega
      have ht2 : 6+2*u+2*v+1 = t := by dsimp [u,v] at *; omega
      rw [hm,ht2] at h
      exact h
/-- Strict log-concavity of both parity subsequences of the explicit
coefficient formula, for every interior triple throughout its support. -/
theorem strict_parity_gap (e odd : Bool) (m t : Int) (ht : 0 ≤ t)
    (hs : t ≤ 2*m - (4 + (if odd then 1 else 0) + (if e then 1 else 0))) :
    (coeff24 e odd m t) * (coeff24 e odd m (t+2)) < (coeff24 e odd m (t+1))^2 := by
  have h : 0 < gap e odd m t := by
    cases e <;> cases odd
    · exact cover00 m t ht hs
    · exact cover01 m t ht hs
    · exact cover10 m t ht hs
    · exact cover11 m t ht hs
  unfold gap at h
  omega

#print axioms SecondDiagonal.strict_parity_gap
end SecondDiagonal
