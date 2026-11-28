module

public import PoleInverse
public import PoleBlock

@[expose] public section

namespace ArctanPole
open Real Finset

private theorem unique_fits {x y : ℤ} {K t : ℝ} (ht : 0 < t) (hb : 2*K < t^5)
    (hx : Fits K t x) (hy : Fits K t y) : x = y := by
  obtain ⟨ex, hex, Hx⟩ := hx
  obtain ⟨ey, hey, Hy⟩ := hy
  have hd : (x:ℝ) - y = (ex-ey)/t^5 := by rw [Hx,Hy]; ring
  have hlt : |(x:ℝ)-y| < 1 := by
    rw [hd, abs_div, abs_of_pos (pow_pos ht 5), div_lt_one (pow_pos ht _)]
    exact (abs_sub _ _).trans_lt ((add_le_add hex hey).trans_lt (by linarith only [hb]))
  obtain ⟨h₁,h₂⟩ := abs_lt.mp hlt
  have h₁' : -1 < x-y := by exact_mod_cast h₁
  have h₂' : x-y < 1 := by exact_mod_cast h₂
  omega

/-- Bound on the number of actual indices with an n⁻⁶-close pole in a large dyadic block. -/
theorem phase_index_block :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : Finset ℕ) (j : ℕ → ℕ) (J : ℕ),
      (∀ n ∈ S, 10 ≤ n ∧ J ≤ j n ∧ j n < 2*J ∧
        |phase n - (j n:ℝ)*(π/2)| ≤ 1/(n:ℝ)^6) →
      (1 ≤ D*(exp (π/2))^J) →
      (1000*budget 200000 ≤ (D*(exp (π/2))^J)^2) →
      ((exp (π/2))^J ≤ (D*(exp (π/2))^J)^2) →
      (400000 < (D*(exp (π/2))^J)^5) →
      S.card*S.card ≤ 2*J + 2*(2*J)*Nat.sqrt (3*(2*J)) := by
  classical
  obtain ⟨C,hC⟩ := phase_pole_fits
  let D := exp (-C)
  let q := exp (π/2)
  have hD : 0 < D := exp_pos _
  have hq : 2 ≤ q := by dsimp [q]; linarith [Real.two_le_pi, add_one_le_exp (π/2)]
  refine ⟨D,hD,fun S j J h hstart herr hwidth huniq => ?_⟩
  have hfit (n : ℕ) (hn : n ∈ S) : Fits 200000 (D*q^(j n)) (2*(n:ℤ)+1) := by
    have heq : D*q^(j n) = exp ((j n:ℝ)*(π/2)-C) := by
      dsimp [D,q]
      rw [sub_eq_add_neg, exp_add, exp_natCast_mul, mul_comm]
    rw [heq]
    exact hC n _ (h n hn).1 (h n hn).2.2.2
  have hinj : Set.InjOn j (↑S) := by
    intro a ha b hb hab
    have hba : Fits 200000 (D*q^(j a)) (2*(b:ℤ)+1) := by simpa only [hab] using hfit b hb
    have hle : D*q^J ≤ D*q^(j a) := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith : 1 ≤ q) (h a ha).2.1) hD.le
    have hbig := huniq.trans_le (pow_le_pow_left₀ (by linarith : 0 ≤ D*q^J) hle 5)
    have hp : 0 < D*q^(j a) := mul_pos hD (pow_pos (by linarith : 0 < q) _)
    have hi := unique_fits (K:=200000) hp (by simpa only [show (2:ℝ)*200000 = 400000 by norm_num] using hbig) (hfit a ha) hba
    omega
  let T := S.image j
  let lift (i : ℕ) : ℕ := if H : ∃ n ∈ S, j n = i then H.choose else 0
  have hlift (i : ℕ) (hi : i ∈ T) : lift i ∈ S ∧ j (lift i) = i := by
    obtain H := mem_image.mp hi
    simpa only [lift, dite_eq_left H] using H.choose_spec
  have hT (i : ℕ) (hi : i ∈ T) : J ≤ i ∧ i < 2*J := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hi
    exact ⟨(h _ hn).2.1, (h _ hn).2.2.1⟩
  let y (i : ℕ) : ℤ := 2*(lift i : ℤ)+1
  have hy (i : ℕ) (hi : i ∈ T) : Fits 200000 (D*q^i) (y i) := by
    obtain ⟨hl,he⟩ := hlift i hi
    simpa only [y, he] using hfit (lift i) hl
  have hcount := pole_block_count hT hD hq hstart herr hwidth hy
  simpa only [T, card_image_of_injOn hinj] using hcount

#print axioms phase_index_block

end ArctanPole

namespace ArctanPole
open Real Set

/-- The tangent argument in the definition of the Amdeberhan--Medina--Moll sequence. -/
noncomputable def angle (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, arctan ((j+1:ℕ):ℝ)

private theorem reflect_angle (n : ℕ) : angle n + phase n = (n:ℝ)*(π/2) := by
  induction n with
  | zero => simp [angle,phase]
  | succ n ih =>
    unfold angle phase at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ, arctan_inv_of_pos (by positivity : 0 < ((n+1:ℕ):ℝ))]
    push_cast at ih ⊢
    linarith

private theorem arctan_small (x : ℝ) : |arctan x| ≤ |x| := by
  suffices H : ∀ y : ℝ, 0 ≤ y → arctan y ≤ y by
    rcases le_total 0 x with hp|hn
    · simpa only [abs_of_nonneg (arctan_nonneg.mpr hp), abs_of_nonneg hp] using H x hp
    · rw [abs_of_nonpos hn, abs_of_nonpos (arctan_le_zero.mpr hn), ←arctan_neg]
      exact H (-x) (neg_nonneg.mpr hn)
  intro y hy
  rcases hy.eq_or_lt with rfl|hy
  · simp
  obtain ⟨c,_,he⟩ := exists_hasDerivAt_eq_slope arctan (fun r => 1/(1+r^2)) hy
    continuous_arctan.continuousOn (fun x _ => hasDerivAt_arctan x)
  rw [arctan_zero, sub_zero, sub_zero] at he
  have h := (eq_div_iff hy.ne').mp he
  have hq : 1/(1+c^2) ≤ (1:ℝ) := by
    rw [div_le_one (by positivity : 0 < 1+c^2)]; nlinarith [sq_nonneg c]
  linarith [mul_le_mul_of_nonneg_right hq hy.le]

/-- Every index with a large tangent is close to a half-period pole of the reciprocal sum. -/
theorem pole_of_large_tangent {n : ℕ} (hn : 10 ≤ n) (hx : (n:ℝ)^6 ≤ |tan (angle n)|) :
    ∃ j : ℕ, |phase n - (j:ℝ)*(π/2)| ≤ 1/(n:ℝ)^6 := by
  let θ := angle n
  let d := arctan (tan θ)⁻¹
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hn6 : 1 ≤ (n:ℝ)^6 := one_le_pow₀ hn1
  have htan : tan θ ≠ 0 := by
    intro h
    change (n:ℝ)^6 ≤ |tan θ| at hx
    rw [h, abs_zero] at hx
    linarith
  have hcos : cos θ ≠ 0 := by intro h; apply htan; simp [tan_eq_sin_div_cos,h]
  have hsin : sin θ ≠ 0 := by intro h; apply htan; simp [tan_eq_sin_div_cos,h]
  have h₁ : cos θ = sin θ*(tan θ)⁻¹ := by rw [tan_eq_sin_div_cos]; field_simp
  have h₂ : sin d = (tan θ)⁻¹*cos d := by
    have h := Real.tan_arctan (tan θ)⁻¹
    change tan d = _ at h
    rw [tan_eq_sin_div_cos, div_eq_iff (cos_arctan_pos _).ne'] at h
    exact h
  have hzero : cos (θ+d) = 0 := by rw [cos_add,h₁,h₂]; ring
  obtain ⟨k,hk⟩ := cos_eq_zero_iff.mp hzero
  let j : ℤ := n-2*k-1
  have hj : phase n - (j:ℝ)*(π/2) = d := by
    dsimp [j]; push_cast
    dsimp [θ] at hk
    linarith [reflect_angle n]
  have hsmall : |d| ≤ 1/(n:ℝ)^6 := by
    apply (arctan_small _).trans
    rw [abs_inv, ←one_div]
    exact one_div_le_one_div_of_le (by positivity) hx
  have hj0 : 0 ≤ j := by
    by_contra! h
    have hneg : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    have hpn : 0 ≤ phase n := by
      unfold phase
      exact Finset.sum_nonneg fun _ _ => arctan_nonneg.mpr (by positivity)
    have hdx := (abs_le.mp hsmall).2
    have h₃ := mul_le_mul_of_nonneg_right hneg (show 0 ≤ π/2 by positivity)
    have h₂n : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have h₅ := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h₂n 6
    norm_num at h₅
    have h₄ := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (show (2:ℝ) ≤ (n:ℝ)^6 by linarith)
    linarith [Real.two_le_pi]
  use j.toNat
  rw [show (j.toNat:ℝ) = (j:ℝ) by exact_mod_cast Int.toNat_of_nonneg hj0,hj]
  exact hsmall

#print axioms pole_of_large_tangent

end ArctanPole

namespace ArctanPole
open Real Finset

/-- Count large values of the literal tangent sum by a dyadic interval of its reciprocal
phase. The starting block threshold depends only on the universal phase constant. -/
theorem high_tangent_block :
    ∃ J₀ : ℕ, ∀ J ≥ J₀, ∀ S : Finset ℕ,
      (∀ n ∈ S, 10 ≤ n ∧ (n:ℝ)^6 ≤ |tan (angle n)| ∧
        ((J:ℝ)-1/2)*(π/2) ≤ phase n ∧ phase n < (2*(J:ℝ)-1/2)*(π/2)) →
      S.card*S.card ≤ 2*J+2*(2*J)*Nat.sqrt (3*(2*J)) := by
  classical
  obtain ⟨D,hD,H⟩ := phase_index_block
  let q := exp (π/2)
  have hq : 2 ≤ q := by dsimp [q]; linarith [Real.two_le_pi, Real.add_one_le_exp (π/2)]
  let M := 1 + 1000*budget 200000 + 400000
  obtain ⟨J₀,hJ₀⟩ := exists_nat_gt (max (M/D) (1/D^2))
  use J₀
  intro J hJ S hs
  have hg (n : ℕ) (hn : n∈S) := pole_of_large_tangent (hs n hn).1 (hs n hn).2.1
  let j (n : ℕ) := if hn : n ∈ S then (hg n hn).choose else 0
  have hsmall (n : ℕ) (hn : n∈S) : |phase n - (j n:ℝ)*(π/2)| ≤ 1/(n:ℝ)^6 := by
    simpa only [j,dite_eq_left hn] using (hg n hn).choose_spec
  have hp : 1 ≤ π/2 := by linarith [Real.two_le_pi]
  have hblocks (n : ℕ) (hn : n∈S) : 10 ≤ n ∧ J ≤ j n ∧ j n < 2*J ∧
      |phase n - (j n:ℝ)*(π/2)| ≤ 1/(n:ℝ)^6 := by
    obtain ⟨hn₁,_,hl,hu⟩ := hs n hn
    obtain ⟨hk₁,hk₂⟩ := abs_le.mp (hsmall n hn)
    have hn₂ : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hb := pow_le_pow_left₀ (by norm_num : 0 ≤ (2:ℝ)) hn₂ 6
    norm_num at hb
    have hb' := one_div_le_one_div_of_le (by norm_num : 0 < (64:ℝ)) hb
    refine ⟨hn₁, ?_, ?_, hsmall n hn⟩
    · by_contra! ht
      have ht' : (j n:ℝ)+1 ≤ (J:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt ht)
      linarith [mul_le_mul_of_nonneg_right ht' (by positivity : 0 ≤ π/2)]
    · by_contra! ht
      have ht' : 2*(J:ℝ) ≤ (j n:ℝ) := by exact_mod_cast ht
      linarith [mul_le_mul_of_nonneg_right ht' (by positivity : 0 ≤ π/2)]
  have hpow : (J₀:ℝ) ≤ q^J := by
    have h₂ : (J:ℝ) ≤ (2:ℝ)^J := by exact_mod_cast (Nat.lt_two_pow_self (n:=J)).le
    exact ((by exact_mod_cast hJ : (J₀:ℝ) ≤ J).trans h₂).trans (pow_le_pow_left₀ (by norm_num) hq _)
  have hM : M ≤ D*q^J := by
    have h := ((le_max_left _ _).trans hJ₀.le).trans hpow
    linarith [(div_le_iff₀ hD).mp h]
  have hw : q^J ≤ (D*q^J)^2 := by
    have h := ((le_max_right _ _).trans hJ₀.le).trans hpow
    have hh := (div_le_iff₀ (pow_pos hD 2)).mp h
    have hqj : 0 ≤ q^J := by dsimp [q]; positivity
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh) hqj]
  have hb₀ : 0 ≤ budget 200000 := by norm_num [budget]
  dsimp [M] at hM
  have h₁ : 1 ≤ D*q^J := by linarith
  have h₂ : D*q^J ≤ (D*q^J)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (show 0 ≤ D*q^J by linarith)]
  have h₅ := pow_le_pow_right₀ h₁ (show 1 ≤ 5 by decide)
  simp only [pow_one] at h₅
  exact H S j J hblocks h₁ (by linarith) hw (by linarith)

#print axioms high_tangent_block

end ArctanPole
