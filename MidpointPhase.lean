module

public import MidpointDerivative

@[expose] public section

namespace ArctanPole
open Real Set Filter
open scoped Topology

private theorem rate_bounds {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1/2) :
    -(4000*s^6) ≤ rate s ∧ rate s ≤ 0 := by
  have sq : s^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hs hs' 2
  have fo : s^4 ≤ (1/2:ℝ)^4 := pow_le_pow_left₀ hs hs' 4
  have hp : (3/4:ℝ)^5 ≤ (1-s^2)^5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
  have hd : 1/2 ≤ 3*(1+4*s^2)*(1-s^2)^5 := by
    nlinarith [mul_nonneg (sq_nonneg s) (show 0 ≤ (1-s^2)^5 by linarith)]
  have hpos : 0 < 3*(1+4*s^2)*(1-s^2)^5 := by linarith
  unfold rate
  constructor
  · apply (le_div_iff₀ hpos).mpr
    have hnum : 1510 + 1388*s^2 + 142*s^4 ≤ 2000 := by linarith
    nlinarith [mul_nonneg (pow_nonneg hs 6) (sub_nonneg.mpr hnum),
      mul_nonneg (pow_nonneg hs 6) (sub_nonneg.mpr hd)]
  · exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg hs 6)) (by positivity)) hpos.le

private theorem err_bounds {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1/2) :
    -(4000*s^7) ≤ err s ∧ err s ≤ 0 := by
  have hcont : ContinuousOn err (Icc 0 s) := fun x hx =>
    (err_deriv hx.1 (hx.2.trans hs')).continuousAt.continuousWithinAt
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope err rate hs hcont
    (fun x hx => err_deriv hx.1.le (hx.2.le.trans hs'))
  have hz : err 0 = 0 := by norm_num [err]
  rw [hz, sub_zero, sub_zero] at he
  have he' := (eq_div_iff hs.ne').mp he
  obtain ⟨hlo,hhi⟩ := rate_bounds hc.1.le (hc.2.le.trans hs')
  have hp := pow_le_pow_left₀ hc.1.le hc.2.le 6
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ rate c + 4000*s^6 by linarith) hs.le]
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg hhi hs.le]

/-- Reciprocal arctangent sum from Ono's Proposition 3.2. -/
noncomputable def phase (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, arctan ((j+1:ℕ) : ℝ)⁻¹

noncomputable def midpoint (z : ℝ) : ℝ := log z + 5/(24*z^2) - 19/(192*z^4)

private theorem err_identity {r : ℝ} (hr : 1 ≤ r) :
    arctan r⁻¹ - (midpoint (r+1/2) - midpoint (r-1/2)) = err (1/(2*r)) := by
  have hr' : 0 < r := by linarith
  have hp : 0 < 1+1/(2*r) := by positivity
  have hq : 0 < 1-1/(2*r) := by
    rw [sub_pos, div_lt_iff₀ (by positivity : 0 < 2*r)]
    linarith
  have hlp : r+1/2 = r*(1+1/(2*r)) := by field_simp
  have hlq : r-1/2 = r*(1-1/(2*r)) := by field_simp
  have h2 : 2*(1/(2*r)) = r⁻¹ := by ring
  unfold err midpoint
  rw [h2, hlp, hlq, log_mul hr'.ne' hp.ne', log_mul hr'.ne' hq.ne']
  field_simp
  ring

noncomputable def rem (n : ℕ) := phase n - midpoint ((n:ℝ)+1/2)

private theorem rem_step (n : ℕ) :
    -(32 / ((n:ℝ)+1)^7) ≤ rem (n+1) - rem n ∧ rem (n+1) - rem n ≤ 0 := by
  let r : ℝ := n+1
  have hr : 1 ≤ r := by dsimp [r]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hr' : 0 < r := by linarith
  have hs : 1/(2*r) ≤ 1/2 := by rw [div_le_iff₀ (by positivity : 0 < 2*r)]; linarith
  obtain ⟨hl, hu⟩ := err_bounds (by positivity : 0 < 1/(2*r)) hs
  have hi : rem (n+1) - rem n = err (1/(2*r)) := by
    unfold rem phase
    rw [Finset.sum_range_succ, Nat.cast_succ, ←err_identity hr]
    change _ = arctan ((n:ℝ)+1)⁻¹ - (midpoint (((n:ℝ)+1)+1/2) - midpoint (((n:ℝ)+1)-1/2))
    rw [show ((n:ℝ)+1)-1/2 = (n:ℝ)+1/2 by ring]
    push_cast
    ring
  rw [hi]
  refine ⟨?_, hu⟩
  change -(32/r^7) ≤ _
  apply le_trans _ hl
  field_simp
  norm_num

private theorem telescope_weight {x : ℝ} (hx : 1 ≤ x) :
    1/(x+1)^7 ≤ 1/x^6 - 1/(x+1)^6 := by
  have hx' : 0 < x := by linarith
  have hxp : 0 < x+1 := by linarith
  field_simp
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem rem_interval (n m : ℕ) (hn : 1 ≤ n) (hm : n ≤ m) :
    rem m ≤ rem n ∧ rem n - 32/(n:ℝ)^6 ≤ rem m - 32/(m:ℝ)^6 := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ m hm ih =>
    obtain ⟨hl,hu⟩ := rem_step m
    have hw := telescope_weight (x:=(m:ℝ)) (by exact_mod_cast hn.trans hm)
    push_cast
    refine ⟨by linarith [ih.1], ?_⟩
    simp only [div_eq_mul_inv,one_mul] at *
    linarith [ih.2]

/-- A sixth-order one-sided remainder on the literal sum, uniform in every positive index. -/
theorem phase_midpoint :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      0 ≤ phase n - (C + midpoint ((n:ℝ)+1/2)) ∧
        phase n - (C + midpoint ((n:ℝ)+1/2)) ≤ 32/(n:ℝ)^6 := by
  let S := rem '' (Set.Ici 1)
  have h1 : rem 1 ∈ S := ⟨1, Set.mem_Ici.mpr (by decide), rfl⟩
  have hb : BddBelow S := by
    use rem 1 - 32
    rintro _ ⟨m,hm,rfl⟩
    have h := (rem_interval 1 m le_rfl hm).2
    norm_num at h
    linarith [show 0 ≤ 32/(m:ℝ)^6 by positivity]
  refine ⟨sInf S, fun n hn => ?_⟩
  have hu : sInf S ≤ rem n := csInf_le hb ⟨n,hn,rfl⟩
  have hl : rem n - 32/(n:ℝ)^6 ≤ sInf S := by
    apply le_csInf ⟨_,h1⟩
    rintro _ ⟨m,hm,rfl⟩
    rcases le_total n m with h|h
    · linarith [(rem_interval n m hn h).2, show 0 ≤ 32/(m:ℝ)^6 by positivity]
    · linarith [(rem_interval m n hm h).1, show 0 ≤ 32/(n:ℝ)^6 by positivity]
  dsimp [rem] at hu hl
  constructor <;> linarith

#print axioms phase_midpoint

end ArctanPole
