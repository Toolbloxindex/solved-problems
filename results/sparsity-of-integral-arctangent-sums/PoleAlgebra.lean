import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace ArctanPole

def b : ℝ := -5/12
def c : ℝ := 13/192

/-- The normalized expansion of an odd integer at a pole, with the remainder coefficient
specified explicitly. The reciprocal scales are u = 1/T² and x = 1/v². -/
def sample (u x err : ℝ) : ℝ := 2 + u * (b*x + u*(c*x^2 + u*err))

private def pair (u x y : ℝ) : ℝ :=
  4 + 2*b*u*(x+y) + u^2*(2*c*(x^2+y^2) + b^2*x*y)

def budget (K : ℝ) : ℝ := 4*K+(1+K)*(2+K)+(1+K)

private theorem linear_bound {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : |b*x| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg hx]
  norm_num [b]
  linarith

private theorem quad_bound {u x e K : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hx : 0 ≤ x) (hx' : x ≤ 1) (he : |e| ≤ K) : |c*x^2 + u*e| ≤ 1+K := by
  calc
    _ ≤ |c*x^2| + |u*e| := abs_add_le _ _
    _ ≤ 1 + K := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x), abs_of_nonneg hu]
      have hx2 : x^2 ≤ 1 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx')]
      apply add_le_add
      · norm_num [c]
        linarith
      · calc
          u * |e| ≤ 1 * |e| := by gcongr
          _ ≤ K := by simpa only [one_mul] using he

private theorem prod_bound {u x y e f K : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (he : |e| ≤ K) (hf : |f| ≤ K) :
    |sample u x e * sample u y f - pair u x y| ≤ u^3 * budget K := by
  let cx := c*x^2 + u*e
  let cy := c*y^2 + u*f
  let ly := b*y + u*cy
  have hk : 0 ≤ K := (abs_nonneg _).trans he
  have hcx : |cx| ≤ 1+K := quad_bound hu hu' hx hx' he
  have hcy : |cy| ≤ 1+K := quad_bound hu hu' hy hy' hf
  have hbx := linear_bound hx hx'
  have hby := linear_bound hy hy'
  have hly : |ly| ≤ 2+K := by
    calc
      _ ≤ |b*y| + |u*cy| := abs_add_le _ _
      _ ≤ 1 + 1*(1+K) := by
        rw [abs_mul u cy, abs_of_nonneg hu]
        gcongr
      _ = _ := by ring
  have herr : sample u x e * sample u y f - pair u x y =
      u^3*(2*(e+f) + cx*ly + (b*x)*cy) := by
    dsimp [sample, pair, cx, cy, ly]
    ring
  rw [herr, abs_mul, abs_of_nonneg (pow_nonneg hu _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  calc
    _ ≤ |2*(e+f) + cx*ly| + |b*x*cy| := abs_add_le _ _
    _ ≤ (|2*(e+f)| + |cx*ly|) + |b*x*cy| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (2*(K+K) + (1+K)*(2+K)) + 1*(1+K) := by
      rw [abs_mul (2 : ℝ), abs_mul cx, abs_mul (b*x)]
      rw [abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      have hef := (abs_add_le e f).trans (add_le_add he hf)
      gcongr
    _ = _ := by unfold budget; ring

structure Corners where
  origin : ℝ
  east : ℝ
  north : ℝ
  diagonal : ℝ

def Corners.Bounded (E : Corners) (K : ℝ) : Prop :=
  |E.origin| ≤ K ∧ |E.east| ≤ K ∧ |E.north| ≤ K ∧ |E.diagonal| ≤ K

/-- Rectangle determinant divided by T²RS. -/
def rect (u r s : ℝ) (E : Corners) : ℝ :=
  sample u 1 E.origin * sample u (r*s) E.diagonal -
  sample u r E.east * sample u s E.north

private def lin (r s : ℝ) := 2*b*(1-r)*(1-s)
private def quad (r s : ℝ) := 2*c*(1-r^2)*(1-s^2)

theorem rect_error {u r s K : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1)
    {E : Corners} (hE : E.Bounded K) :
    |rect u r s E - (u*lin r s + u^2*quad r s)| ≤ 2*u^3*budget K := by
  have hrs : r*s ≤ 1 := (mul_le_mul hr' hs' hs zero_le_one).trans_eq (one_mul 1)
  have h₀ := prod_bound hu hu' (show (0:ℝ) ≤ 1 by norm_num) le_rfl
    (mul_nonneg hr hs) hrs hE.1 hE.2.2.2
  have h₁ := prod_bound hu hu' hr hr' hs hs' hE.2.1 hE.2.2.1
  have heq : pair u 1 (r*s) - pair u r s = u*lin r s + u^2*quad r s := by
    dsimp [pair, lin, quad]
    ring
  rw [← heq, rect, show
    sample u 1 E.origin * sample u (r*s) E.diagonal - sample u r E.east * sample u s E.north -
    (pair u 1 (r*s) - pair u r s) =
    (sample u 1 E.origin * sample u (r*s) E.diagonal - pair u 1 (r*s)) -
    (sample u r E.east * sample u s E.north - pair u r s) by ring]
  exact (abs_sub _ _).trans ((add_le_add h₀ h₁).trans_eq (by ring))

private theorem leading_bounds {r s l : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1/2)
    (hs : 0 ≤ s) (hs' : s ≤ 1/2) (hl : 0 ≤ l) (hl' : l ≤ 1/2) :
    1/64 ≤ quad r s * (1-l) ∧ quad r s * (1-l) ≤ 1/2 := by
  have rb : 3/4 ≤ 1-r^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr') (add_nonneg hr (by norm_num : 0 ≤ (1:ℝ)/2))]
  have sb : 3/4 ≤ 1-s^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs') (add_nonneg hs (by norm_num : 0 ≤ (1:ℝ)/2))]
  have rb' : 1-r^2 ≤ 1 := by linarith [sq_nonneg r]
  have sb' : 1-s^2 ≤ 1 := by linarith [sq_nonneg s]
  dsimp [quad, c]
  constructor
  · calc
      (1:ℝ)/64 ≤ 2*(13/192)*(3/4)*(3/4)*(1/2) := by norm_num
      _ ≤ _ := by
        have : (1:ℝ)/2 ≤ 1-l := by linarith
        gcongr
  · calc
      _ ≤ 2*((13:ℝ)/192)*1*1*1 := by
        have : 1-l ≤ 1 := by linarith
        gcongr; linarith
      _ ≤ _ := by norm_num

/-- Two integer rectangles with the indicated scaled expansions cannot be translates.
The shift ratios are inverse squares, while V is the positive product scale T²RS. -/
theorem rectangle_conflict {u r s l K V : ℝ} (hu : 0 < u) (hu' : u ≤ 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1/2) (hs : 0 ≤ s) (hs' : s ≤ 1/2)
    (hl : 0 < l) (hl' : l ≤ 1/2) (hV : 0 < V) (hsmall : V*u^2 ≤ 1)
    (ht : 1000*u*budget K ≤ 1) {E F : Corners} (hE : E.Bounded K) (hF : F.Bounded K)
    {d d' : ℤ} (hd : (d:ℝ) = V*rect u r s E) (hd' : l*(d':ℝ) = V*rect (u*l) r s F) :
    False := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hE.1
  have hM : 0 ≤ budget K := by dsimp [budget]; positivity
  have hl1 : l ≤ 1 := by linarith
  have hr1 : r ≤ 1 := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hu2 : 0 < u^2 := pow_pos hu _
  have hul1 : u*l ≤ 1 := (mul_le_mul hu' hl1 hl.le zero_le_one).trans_eq (one_mul 1)
  let A := rect u r s E - (u*lin r s + u^2*quad r s)
  let B := (rect (u*l) r s F - (u*l*lin r s + (u*l)^2*quad r s))/l
  have hA : |A| ≤ 2*u^3*budget K := rect_error hu.le hu' hr hr1 hs hs1 hE
  have hB : |B| ≤ 2*u^3*budget K := by
    dsimp [B]
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl]
    have hl2 : l^2 ≤ 1 := by nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hl1)]
    calc
      _ ≤ 2*(u*l)^3*budget K := rect_error (mul_nonneg hu.le hl.le) hul1 hr hr1 hs hs1 hF
      _ = (2*u^3*budget K*l)*l^2 := by ring
      _ ≤ (2*u^3*budget K*l)*1 := by gcongr
      _ = _ := by ring
  obtain ⟨hab, hba⟩ := abs_le.mp ((abs_sub A B).trans (add_le_add hA hB))
  obtain ⟨hlow, hhigh⟩ := leading_bounds hr hr' hs hs' hl.le hl'
  have ht' : 1000*(u^3*budget K) ≤ u^2 := by
    calc
      _ = u^2*(1000*u*budget K) := by ring
      _ ≤ u^2*1 := mul_le_mul_of_nonneg_left ht hu2.le
      _ = _ := mul_one _
  have low := mul_le_mul_of_nonneg_left hlow hu2.le
  have high := mul_le_mul_of_nonneg_left hhigh hu2.le
  set Z := u^2*(quad r s*(1-l)) + (A-B)
  have hZ : 0 < Z ∧ Z < u^2 := by
    dsimp only [Z]
    constructor <;> linarith
  have hd'' : (d':ℝ) = V*rect (u*l) r s F /l := (eq_div_iff hl.ne').mpr (by linarith)
  have heq : (d:ℝ) - (d':ℝ) = V*Z := by
    rw [hd, hd'']
    dsimp [Z, A, B]
    field_simp
    ring
  have hp : (0:ℝ) < (d:ℝ) - (d':ℝ) := heq ▸ mul_pos hV hZ.1
  have hlt : (d:ℝ) - (d':ℝ) < 1 :=
    heq ▸ (mul_lt_mul_of_pos_left hZ.2 hV).trans_le hsmall
  have hpi : 0 < d-d' := by exact_mod_cast hp
  have hlti : d-d' < 1 := by exact_mod_cast hlt
  omega

end ArctanPole
