module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr

@[expose] public section

namespace ArctanPole
open Real Filter

/-- The fixed factorial block has enough exponential growth to absorb Chebyshev's
LCM estimate and every fixed power of the index. -/
theorem block_growth (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ, 0 < L →
      log (L:ℝ) ≤ log 4 * (2*n) + 2 * sqrt (2*n) * log (2*n) →
      (L:ℝ) * (n:ℝ)^r < (2:ℝ)^(4361*(n/1024)) := by
  have h2 : 0 < log 2 := log_pos (by norm_num)
  let e := log 2 / 256
  have he : 0 < e := by dsimp [e]; positivity
  have hlog := (isLittleO_log_rpow_atTop (r:=(1/2:ℝ)) (by norm_num)).bound he
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.1 hlog
  obtain ⟨b,hb⟩ := exists_nat_gt (max T (max ((r:ℝ)^2) 100000))
  use b
  intro n hn L hL hLc
  have hnR : (b:ℝ) ≤ n := by exact_mod_cast hn
  have hTn : T ≤ n := (le_max_left _ _).trans (hb.le.trans hnR)
  have hbase := (le_max_right T (max ((r:ℝ)^2) 100000)).trans (hb.le.trans hnR)
  have hrn : (r:ℝ)^2 ≤ n := (le_max_left _ _).trans hbase
  have hnlarge : (100000:ℝ) ≤ n := (le_max_right _ _).trans hbase
  have hn0 : 0 < (n:ℝ) := by linarith
  have hsmall (x : ℝ) (hx : T ≤ x) (hx' : 1 ≤ x) : log x ≤ e*sqrt x := by
    have h := hT x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (log_nonneg hx'), ←Real.sqrt_eq_rpow,
                abs_of_nonneg (sqrt_nonneg _)] using h
  have h1 := hsmall n hTn (by linarith)
  have h2n := hsmall (2*n) (by linarith) (by linarith)
  have hrr : (r:ℝ) ≤ sqrt n := (Real.le_sqrt (by positivity) (by positivity)).mpr hrn
  have herr : 2 * sqrt (2*n) * log (2*n) ≤ 4*e*n := by
    have H := mul_le_mul_of_nonneg_left h2n (sqrt_nonneg (2*n))
    nlinarith only [H,Real.sq_sqrt (show 0 ≤ 2*(n:ℝ) by positivity),
      congrArg (fun t => e*t) (Real.sq_sqrt (show 0 ≤ 2*(n:ℝ) by positivity))]
  have hpoly : (r:ℝ)*log n ≤ e*n := by
    calc
      _ ≤ sqrt n * (e*sqrt n) := mul_le_mul hrr h1 (log_nonneg (by linarith)) (sqrt_nonneg _)
      _ = _ := by rw [←mul_left_comm,Real.mul_self_sqrt hn0.le]
  have hdiv : (n:ℝ)-1024 ≤ 1024*((n/1024:ℕ):ℝ) := by
    have : n ≤ 1024*(n/1024)+1024 := by omega
    exact sub_le_iff_le_add.mpr (by exact_mod_cast this)
  have hd := mul_le_mul_of_nonneg_right hdiv h2.le
  have hmargin : 4361*log 2 < (n:ℝ)*log 2/8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hnlarge h2.le, h2]
  have h4 : log 4 = 2*log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have hL0 : 0 < (L:ℝ) := by exact_mod_cast hL
  apply (log_lt_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul hL0.ne' (pow_ne_zero _ hn0.ne'), Real.log_pow, Real.log_pow]
  push_cast
  dsimp only [e] at herr hpoly
  rw [h4] at hLc
  have hnc := mul_nonneg hn0.le h2.le
  ring_nf at hLc herr hpoly hd hmargin hnc ⊢
  linarith only [hLc,herr,hpoly,hd,hmargin,hnc]

#print axioms block_growth

end ArctanPole
