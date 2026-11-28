module

public import IntegralCount

@[expose] public section

namespace ArctanPole
open Real Finset MollRigidity Filter Asymptotics

/-- Number of integral values in the conjectured empty interval, including its finite prefix. -/
def integralCount (N : ℕ) : ℕ :=
  ((Icc 5 N).filter fun n => (gaussProd n).re ∣ (gaussProd n).im).card

/-- A sublogarithmic upper bound on the count for the original divisibility predicate. -/
theorem integral_count_isBigO :
    (fun N : ℕ => (integralCount N : ℝ)) =O[atTop]
      (fun N : ℕ => (log (N:ℝ)) ^ (3/4 : ℝ)) := by
  obtain ⟨a,ha⟩ := integral_index_count
  obtain ⟨b,hb⟩ := exists_nat_gt (exp 1)
  refine isBigO_iff.mpr ⟨(a:ℝ)+5120, eventually_atTop.mpr ⟨max a b, ?_⟩⟩
  intro N hN
  have hnb : (b:ℝ) ≤ N := by exact_mod_cast (le_max_right a b).trans hN
  have hl : 1 ≤ log (N:ℝ) := by
    simpa only [log_exp] using log_le_log (exp_pos 1) (hb.le.trans hnb)
  have hl0 : 0 ≤ log (N:ℝ) := by linarith
  let u := (log (N:ℝ)) ^ (3/4 : ℝ)
  have hu : 1 ≤ u := one_le_rpow hl (by norm_num)
  have hu0 : 0 ≤ u := by linarith
  have hpow : u^4 = (log (N:ℝ))^3 := by
    dsimp only [u]
    rw [← rpow_mul_natCast hl0]
    norm_num
  let I := (Icc 5 N).filter fun n => (gaussProd n).re ∣ (gaussProd n).im
  let T := I.filter fun n => a ≤ n
  have hsub : I ⊆ range a ∪ T := by
    intro n hn
    by_cases h : a ≤ n
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,h⟩)
    · exact mem_union_left _ (mem_range.mpr (Nat.lt_of_not_ge h))
  have hcard := (card_le_card hsub).trans (card_union_le ..)
  rw [card_range] at hcard
  have htail := ha N ((le_max_left a b).trans hN) T (by
    intro n hn
    obtain ⟨hn,ha⟩ := mem_filter.mp hn
    obtain ⟨hn,hd⟩ := mem_filter.mp hn
    exact ⟨ha,(mem_Icc.mp hn).2,hd⟩)
  have hroot : (T.card:ℝ) ≤ 5120*u := by
    apply le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (by positivity)
    rw [mul_pow,hpow]
    nlinarith only [htail, pow_nonneg hl0 3]
  change ‖(I.card:ℝ)‖ ≤ ((a:ℝ)+5120)*‖u‖
  rw [Real.norm_of_nonneg (show 0 ≤ (I.card:ℝ) by positivity), Real.norm_of_nonneg hu0]
  have hc : (I.card:ℝ) ≤ (a:ℝ)+T.card := by exact_mod_cast hcard
  nlinarith only [hc,hroot, mul_nonneg (show (0:ℝ) ≤ a by positivity) (sub_nonneg.mpr hu)]

#print axioms integral_count_isBigO

end ArctanPole
