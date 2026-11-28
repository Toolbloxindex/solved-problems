import PoleAlgebra

noncomputable section
namespace ArctanPole

/-- The inverse pole expansion has an absolute remainder bounded by K/t⁵. -/
def Fits (K t : ℝ) (y : ℤ) : Prop :=
  ∃ e : ℝ, |e| ≤ K ∧ (y:ℝ) = 2*t - 5/(12*t) + 13/(192*t^3) + e/t^5

private theorem scaled {K T v : ℝ} (hT : 0 < T) (hv : 1 ≤ v) {y : ℤ}
    (H : Fits K (T*v) y) :
    ∃ e, |e| ≤ K ∧ (y:ℝ) = (T*v)*sample (1/T^2) (1/v^2) e := by
  obtain ⟨err, herr, hy⟩ := H
  have hv0 : 0 < v := by linarith
  have hv6 : 1 ≤ v^6 := one_le_pow₀ hv
  refine ⟨err/v^6, ?_, ?_⟩
  · rw [abs_div, abs_of_pos (pow_pos hv0 _), div_le_iff₀ (pow_pos hv0 _)]
    exact herr.trans (le_mul_of_one_le_right ((abs_nonneg _).trans herr) hv6)
  · rw [hy]
    dsimp [sample, b, c]
    field_simp
    ring

structure IntCorners where
  origin : ℤ
  east : ℤ
  north : ℤ
  diagonal : ℤ

def IntCorners.det (Y : IntCorners) := Y.origin*Y.diagonal - Y.east*Y.north

def IntCorners.FitsAt (Y : IntCorners) (K T R S : ℝ) : Prop :=
  Fits K T Y.origin ∧ Fits K (T*R) Y.east ∧ Fits K (T*S) Y.north ∧
  Fits K (T*(R*S)) Y.diagonal

private theorem rect_measure {K T R S : ℝ} (hT : 0 < T) (hR : 1 ≤ R) (hS : 1 ≤ S)
    {Y : IntCorners} (H : Y.FitsAt K T R S) :
    ∃ E : Corners, E.Bounded K ∧
    (Y.det : ℝ) = T^2*R*S * rect (1/T^2) (1/R^2) (1/S^2) E := by
  obtain ⟨e₀, he₀, h₀⟩ := scaled (v := 1) hT le_rfl (by simpa only [mul_one] using H.1)
  obtain ⟨e₁, he₁, h₁⟩ := scaled hT hR H.2.1
  obtain ⟨e₂, he₂, h₂⟩ := scaled hT hS H.2.2.1
  have hrs : 1 ≤ R*S := one_le_mul_of_one_le_of_one_le hR hS
  obtain ⟨e₃, he₃, h₃⟩ := scaled hT hrs H.2.2.2
  refine ⟨⟨e₀,e₁,e₂,e₃⟩, ⟨he₀,he₁,he₂,he₃⟩, ?_⟩
  have hv : 1/(R*S)^2 = (1/R^2)*(1/S^2) := by simp [mul_pow, mul_comm]
  simp only [one_pow, div_one, mul_one] at h₀
  rw [hv] at h₃
  dsimp [IntCorners.det, rect]
  push_cast
  rw [h₀, h₁, h₂, h₃]
  ring

/-- No eight integer observations can fit both rectangles of the inverse pole expansion
at sufficiently large scale when RS ≤ T². Each positive shift ratio may be different. -/
theorem no_cube_of_fits {K T R S L : ℝ} (hT : 1 ≤ T) (hR : 2 ≤ R)
    (hS : 2 ≤ S) (hL : 2 ≤ L) (herror : 1000*budget K ≤ T^2) (hwidth : R*S ≤ T^2)
    {Y Z : IntCorners} (H : Y.FitsAt K T R S) (H' : Z.FitsAt K (T*L) R S) : False := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hS1 : 1 ≤ S := by linarith
  obtain ⟨E, hE, hd⟩ := rect_measure hT0 hR1 hS1 H
  obtain ⟨F, hF, hd'⟩ := rect_measure (mul_pos hT0 hL0) hR1 hS1 H'
  have small (x : ℝ) (hx : 2 ≤ x) : 1/x^2 ≤ 1/2 := by
    have hx0 : 0 < x := by linarith
    rw [div_le_div_iff₀ (pow_pos hx0 _) (by norm_num)]
    nlinarith [sq_nonneg (x-2)]
  have hl : 1/(T*L)^2 = 1/T^2 * (1/L^2) := by simp [mul_pow, mul_comm]
  apply rectangle_conflict (u := 1/T^2) (r := 1/R^2) (s := 1/S^2) (l := 1/L^2)
    (V := T^2*R*S) (d := Y.det) (d' := Z.det) (by positivity) ?_
    (by positivity) (small R hR) (by positivity) (small S hS) (by positivity) (small L hL)
    (by positivity) ?_ ?_ hE hF hd ?_
  · exact (div_le_one (pow_pos hT0 _)).mpr (one_le_pow₀ hT)
  · field_simp
    nlinarith [mul_le_mul_of_nonneg_left hwidth (sq_nonneg T)]
  · field_simp
    linarith
  · rw [hd', hl]
    field_simp

end ArctanPole
