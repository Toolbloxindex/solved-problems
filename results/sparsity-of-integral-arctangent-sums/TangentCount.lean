import TangentBlocks
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

namespace ArctanPole
open Finset

private theorem card_bound_scale {x J k : ℕ}
    (h : x*x ≤ 2*J+2*(2*J)*Nat.sqrt (3*(2*J))) (hJ : J ≤ 8*16^k) :
    x ≤ 16*8^k := by
  have h4 : (4^k)^2 = 16^k := by rw [pow_right_comm]; norm_num
  have h64 : 16^k*4^k = 8^k*8^k := by rw [←mul_pow,←mul_pow]; norm_num
  have hu : Nat.sqrt (3*(2*J)) ≤ 7*4^k := by
    have H := Nat.sqrt_le' (3*(2*J))
    by_contra! h'
    have H' := Nat.pow_le_pow_left (show 7*4^k+1 ≤ Nat.sqrt (3*(2*J)) by omega) 2
    nlinarith only [H,H',hJ,h4,Nat.zero_le (4^k),Nat.zero_le (16^k)]
  have hh := Nat.mul_le_mul hJ hu
  have h16 : 16^k ≤ 16^k*4^k := Nat.le_mul_of_pos_right _ (by positivity)
  by_contra! h'
  have H := Nat.mul_self_le_mul_self (show 16*8^k+1 ≤ x by omega)
  nlinarith only [hh, hJ,h16,h64,H,h,Nat.zero_le (8^k)]

/-- The fourth power of a count with the dyadic cube estimate grows at most cubically
in the range of labels. Several indices may initially have the same label. -/
theorem aggregate_blocks {S : Finset ℕ} {j : ℕ → ℕ} {L : ℕ} (hL : 0 < L)
    (hr : ∀ n ∈ S, 0 < j n ∧ j n ≤ L)
    (hblock : ∀ J : ℕ, 0<J → let b := (S.filter (fun n => J ≤ j n ∧ j n < 2*J)).card
          b*b ≤ 2*J+2*(2*J)*Nat.sqrt (3*(2*J))) :
    S.card^4 ≤ 64^4*(16*L)^3 := by
  let A (x : ℕ) := (S.filter (fun n => j n < x)).card
  let B (x : ℕ) := (S.filter (fun n => x ≤ j n ∧ j n < 2*x)).card
  have hdouble (x : ℕ) : A (2*x) ≤ A x + B x := by
    apply (card_le_card (t:= (S.filter (fun n => j n < x)) ∪
      S.filter (fun n => x ≤ j n ∧ j n < 2*x)) ?_).trans (card_union_le ..)
    intro n hn
    obtain ⟨hn,hn'⟩ := mem_filter.mp hn
    by_cases h : j n < x
    · exact mem_union_left _ (mem_filter.mpr ⟨hn,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,by omega,hn'⟩)
  have hprefix (k : ℕ) : A (16^k) ≤ 64*8^k := by
    induction k with
    | zero =>
      have he : (S.filter fun n => j n < 1) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hm,hj⟩ := mem_filter.mp hn
        have := (hr _ hm).1
        omega
      simp only [pow_zero, A, he, card_empty, mul_one, Nat.zero_le]
    | succ k ih =>
      have bt (r : ℕ) (hr : 0<r) (hr' : r≤8) : B (r*16^k) ≤ 16*8^k := by
        apply card_bound_scale (hblock _ (by positivity))
        exact Nat.mul_le_mul_right _ hr'
      have h₁ := hdouble (16^k)
      have h₂ := hdouble (2*16^k)
      have h₄ := hdouble (4*16^k)
      have h₈ := hdouble (8*16^k)
      have b₁ := bt 1 (by decide) (by decide)
      have b₂ := bt 2 (by decide) (by decide)
      have b₄ := bt 4 (by decide) (by decide)
      have b₈ := bt 8 (by decide) (by decide)
      simp only [one_mul] at b₁
      rw [←mul_assoc] at h₂ h₄ h₈
      norm_num at h₂ h₄ h₈
      rw [pow_succ, pow_succ, mul_comm (16^k)]
      omega
  let k := (Nat.log 16 L)+1
  have hbound : L < 16^k := Nat.lt_pow_succ_log_self (by decide) L
  have he : (S.filter fun n => j n < 16^k) = S := by
    exact filter_true_of_mem fun n hn => (hr n hn).2.trans_lt hbound
  have ha := hprefix k
  dsimp only [A] at ha
  rw [he] at ha
  have hpow : 16^k ≤ 16*L := by
    dsimp only [k]; rw [pow_succ,mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ hL.ne')
  calc
    _ ≤ (64*8^k)^4 := Nat.pow_le_pow_left ha 4
    _ = 64^4*(16^k)^3 := by rw [mul_pow,pow_right_comm (8:ℕ),pow_right_comm (16:ℕ)]; norm_num
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow 3)

end ArctanPole

namespace ArctanPole
open Real Finset

private theorem coarse_phase :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |phase n - (C+log n)| ≤ 36 := by
  obtain ⟨C,H⟩ := phase_midpoint
  use C
  intro n hn
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  let z := (n:ℝ)+1/2
  have hz : 1 ≤ z := by dsimp [z]; linarith
  have hn0 : 0 < (n:ℝ) := by linarith
  have hz0 : 0 < z := by linarith
  have hu0 := Real.log_le_log hn0 (show (n:ℝ) ≤ z by dsimp [z]; linarith)
  have hule := Real.log_le_log hz0 (show z ≤ 2*(n:ℝ) by dsimp [z]; linarith)
  rw [Real.log_mul (by norm_num) hn0.ne'] at hule
  have hlo := (H n hn).1
  have hhi := (H n hn).2
  change 0 ≤ phase n-(C+midpoint z) at hlo
  change phase n-(C+midpoint z) ≤ 32/(n:ℝ)^6 at hhi
  have hpos : 0 ≤ 5/(24*z^2) := by positivity
  have hpos' : 0 ≤ 19/(192*z^4) := by positivity
  have h₁ : 5/(24*z^2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [show 1 ≤ z^2 from one_le_pow₀ hz]
  have h₂ : 19/(192*z^4) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [show 1 ≤ z^4 from one_le_pow₀ hz]
  have h₃ : 32/(n:ℝ)^6 ≤ 32 := by rw [div_le_iff₀ (by positivity)]; linarith [show 1 ≤ (n:ℝ)^6 from one_le_pow₀ hn']
  unfold midpoint at hlo hhi
  have hlog := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  apply abs_le.mpr
  constructor <;> linarith

/-- A global bound on all sufficiently late indices with a large tangent. The fourth power
form avoids fractional powers and implies O((log N)^(3/4)) after the finite initial segment. -/
theorem large_tangent_count :
    ∃ n₀ : ℕ, ∀ N ≥ n₀, ∀ S : Finset ℕ,
      (∀ n ∈ S, n₀ ≤ n ∧ n ≤ N ∧ (n:ℝ)^6 ≤ |tan (angle n)|) →
      (S.card:ℝ)^4 ≤ 64^4*(80*log N)^3 := by
  classical
  obtain ⟨J₀,H⟩ := high_tangent_block
  obtain ⟨C,hC⟩ := coarse_phase
  let a := π/2
  have ha : 1 ≤ a := by dsimp [a]; linarith [Real.two_le_pi]
  have ha0 : 0 < a := by linarith
  let K := (2*(J₀:ℝ)+2)*a+|C|+40
  obtain ⟨b,hb⟩ := exists_nat_gt (exp K)
  let n₀ := max 10 b
  use n₀
  intro N hN S hs
  have hn₀ {n : ℕ} (hn : n₀ ≤ n) : 10 ≤ n := (le_max_left _ _).trans hn
  have hlog {n : ℕ} (hn : n₀ ≤ n) : K ≤ log n := by
    have hb' : b ≤ n := (le_max_right _ _).trans hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := hn₀ hn; omega)
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    exact hb.le.trans (by exact_mod_cast hb')
  have hKN := hlog hN
  have hKpos : 1 ≤ K := by dsimp [K]; nlinarith [mul_nonneg (Nat.cast_nonneg J₀) ha0.le,abs_nonneg C]
  have hNlog : 1 ≤ log N := hKpos.trans hKN
  let L := ⌊3*log N⌋₊+1
  let j (n : ℕ) := ⌊phase n/a + 1/2⌋₊
  have hJ (n : ℕ) (hn : n∈S) : 2*J₀+1 ≤ j n ∧ j n ≤ L := by
    obtain ⟨hlo,hhi,_⟩ := hs n hn
    have hn' : 1 ≤ n := by have := hn₀ hlo; omega
    have hpn := abs_le.mp (hC n hn')
    have hln := hlog hlo
    have hln' : log (n:ℝ) ≤ log N := log_le_log (by positivity) (by exact_mod_cast hhi)
    have hpos : 0 ≤ phase n := by unfold phase; exact sum_nonneg fun _ _ => arctan_nonneg.mpr (by positivity)
    constructor
    · apply Nat.le_floor
      push_cast
      rw [←sub_le_iff_le_add,le_div_iff₀ ha0]
      dsimp [K] at hln
      linarith [neg_abs_le C]
    · have hupper : phase n/a ≤ phase n := (div_le_self hpos ha)
      have h₁ : C ≤ log N-36 := by
        dsimp [K] at hKN
        nlinarith [le_abs_self C,mul_nonneg (Nat.cast_nonneg J₀) ha0.le]
      apply (Nat.floor_le_floor (show phase n/a+1/2 ≤ 3*log N by linarith [hpn.2])).trans
      exact Nat.le_succ _
  have hblock (J : ℕ) (hJp : 0<J) :
      let f := (S.filter fun n => J ≤ j n ∧ j n < 2*J).card
      f*f ≤ 2*J+2*(2*J)*Nat.sqrt (3*(2*J)) := by
    by_cases hj₀ : J₀ ≤ J
    · apply H J hj₀
      intro n hn
      obtain ⟨hsn,h₁,h₂⟩ := mem_filter.mp hn
      have hl := hs n hsn
      refine ⟨hn₀ hl.1, hl.2.2, ?_, ?_⟩
      · have hfloor := Nat.floor_le (show 0 ≤ phase n/a+1/2 by
          have : 0 ≤ phase n := by unfold phase; exact sum_nonneg fun _ _ => arctan_nonneg.mpr (by positivity)
          positivity)
        have hj' : (J:ℝ) ≤ (j n:ℝ) := by exact_mod_cast h₁
        have big : (J:ℝ)-1/2 ≤ phase n/a := by change (J:ℝ) ≤ ⌊_⌋₊ at hj'; linarith
        exact (le_div_iff₀ ha0).mp big
      · have hh := Nat.lt_of_floor_lt h₂
        change phase n/a+1/2 < ↑(2*J) at hh
        push_cast at hh
        exact (div_lt_iff₀ ha0).mp (by linarith)
    · have he : (S.filter fun n => J ≤ j n ∧ j n < 2*J) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hn,_,hh⟩ := mem_filter.mp hn
        have := (hJ n hn).1
        omega
      simp [he]
  have hc := aggregate_blocks (show 0<L by dsimp [L]; omega)
    (fun n hn => ⟨by have := (hJ n hn).1; omega, (hJ n hn).2⟩) hblock
  have hc' : (S.card:ℝ)^4 ≤ 64^4*(16*(L:ℝ))^3 := by exact_mod_cast hc
  have hL : (L:ℝ) ≤ 5*log N := by
    dsimp [L]; push_cast
    linarith [Nat.floor_le (show 0 ≤ 3*log N by linarith)]
  apply hc'.trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ 16*(L:ℝ))
    (by linarith only [hL] : 16*(L:ℝ) ≤ 80*log N) 3) (by positivity)

#print axioms large_tangent_count

end ArctanPole
