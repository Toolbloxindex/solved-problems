module

public import JacobiProjectiveBase
public import JacobiRankTwoSource
public import Mathlib.Algebra.Polynomial.Homogenize

@[expose] public section

namespace JacobiProjective

open Polynomial JacobiDiagonalControls JacobiRankTwo JacobiRankTwoSource

private noncomputable def inverseCoords : Fin 2 → ℝ[X] := ![X,1-X]

/-- Homogeneous substitution of x and 1-x into a projective polynomial. -/
noncomputable def inverse (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  MvPolynomial.aeval inverseCoords (p.homogenize d)

theorem inverse_mul {d e : ℕ} {p q : ℝ[X]} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ e) :
    inverse (d+e) (p*q) = inverse d p * inverse e q := by
  simp [inverse, homogenize_mul p q hp hq]

theorem inverse_C (d : ℕ) (c : ℝ) : inverse d (C c) = C c*(1-X)^d := by
  simp [inverse, inverseCoords, homogenize_C]

theorem inverse_monomial {i d : ℕ} (hi : i ≤ d) (c : ℝ) :
    inverse d (monomial i c) = C c*X^i*(1-X)^(d-i) := by
  rw [inverse, homogenize_monomial hi, MvPolynomial.aeval_monomial]
  simp [inverseCoords, Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc]

theorem inverse_eq_sum {d : ℕ} (p : ℝ[X]) (hd : p.natDegree ≤ d) :
    inverse d p = ∑ i ∈ p.support, C (p.coeff i)*X^i*(1-X)^(d-i) := by
  classical
  calc
    inverse d p = inverse d (∑ i ∈ p.support, monomial i (p.coeff i)) :=
      congrArg (inverse d) p.sum_monomial_eq.symm
    _ = _ := by
      rw [inverse, homogenize_finsetSum, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact inverse_monomial ((le_natDegree_of_mem_supp i hi).trans hd) _

theorem inverse_linear (r : ℝ) : inverse 1 (X-C r) = X-C r*(1-X) := by
  simp [inverse, inverseCoords, homogenize_sub, homogenize_X, homogenize_C]

theorem inverse_linear_at_pole : inverse 1 (X-C (-1)) = 1 := by
  rw [inverse_linear]
  simp [C_neg]

private theorem inverse_linear_splits (r : ℝ) : (inverse 1 (X-C r)).Splits := by
  rw [inverse_linear, show X-C r*(1-X) = C (1+r)*X-C r by simp [C_add]; ring]
  apply Splits.of_natDegree_le_one
  have hd : (C (1+r)*X).natDegree ≤ 1 := by
    calc
      _ ≤ (C (1+r)).natDegree + (X : ℝ[X]).natDegree := natDegree_mul_le
      _ = 1 := by simp
  have hc : (C r).natDegree ≤ 1 := by rw [natDegree_C]; decide
  exact natDegree_sub_le_of_le hd hc

private theorem one_sub_splits : (1-X : ℝ[X]).Splits := by
  have h : (1-X : ℝ[X]) = -(X-C 1) := by simp
  rw [h]
  exact (Splits.X_sub_C (1 : ℝ)).neg

private theorem inverse_rootProduct_splits (rs : Multiset ℝ) (d : ℕ) (h : rs.card ≤ d) :
    (inverse d (rs.map (X-C ·)).prod).Splits := by
  induction rs using Multiset.induction_on generalizing d with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, ← C_1, inverse_C, C_1, one_mul]
    exact one_sub_splits.pow d
  | cons r rs ih =>
    have hn : rs.card ≤ d-1 := by simp only [Multiset.card_cons] at h; omega
    have hd : d = 1+(d-1) := by simp only [Multiset.card_cons] at h; omega
    rw [Multiset.map_cons, Multiset.prod_cons]
    rw [hd, inverse_mul (show (X-C r).natDegree ≤ 1 by simp)
      (by simpa using hn)]
    exact (inverse_linear_splits r).mul (ih (d-1) hn)

theorem inverse_splits {p : ℝ[X]} {d : ℕ} (hp : p.Splits) (hd : p.natDegree ≤ d) :
    (inverse d p).Splits := by
  have hr := hp.natDegree_eq_card_roots
  have hle : (p.roots.map (X-C ·)).prod.natDegree ≤ d := by simpa [← hr] using hd
  rw [hp.eq_prod_roots]
  rw [← Nat.zero_add d, inverse_mul (by simp) hle, inverse_C]
  exact ((Splits.C _).mul (one_sub_splits.pow 0)).mul
    (inverse_rootProduct_splits p.roots d (hr ▸ hd))

theorem inverse_eval {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d)
    {x : ℝ} (hx : x ≠ 1) :
    (inverse d p).eval x = p.eval (x/(1-x))*(1-x)^d := by
  have h : (evalRingHom x).comp (MvPolynomial.aeval inverseCoords).toRingHom =
      MvPolynomial.eval ![x,(1-x)] := by
    ext i
    · simp
    · fin_cases i <;> simp [inverseCoords]
  change ((evalRingHom x).comp (MvPolynomial.aeval inverseCoords).toRingHom) (p.homogenize d) = _
  rw [h]
  exact eval_homogenize hp _ (by simpa using sub_ne_zero.mpr hx.symm)

private theorem step_degree_le (a b : ℝ) (p : ℝ[X]) :
    (step a b p).natDegree ≤ p.natDegree+1 := by
  unfold step
  apply natDegree_add_le_of_degree_le
  · by_cases h : p.natDegree = 0
    · obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp h
      simp
    · have hh := natDegree_mul_le (p := X*(1+X)) (q := p.derivative)
      have hd := natDegree_mul_le (p := X) (q := (1+X : ℝ[X]))
      have he : (1+X : ℝ[X]).natDegree ≤ 1 := by
        exact natDegree_add_le_of_degree_le (by simp) (by simp)
      have hf := natDegree_derivative_le p
      have hx : (X : ℝ[X]).natDegree = 1 := natDegree_X
      omega
  · have h : (C a + C b*X : ℝ[X]).natDegree ≤ 1 := by
      apply natDegree_add_le_of_degree_le
      · simp
      · have hm := natDegree_mul_le (p := C b) (q := (X : ℝ[X]))
        simpa using hm
    have hm := natDegree_mul_le (p := C a + C b*X) (q := p)
    omega

theorem projective_degree_le (u : ℝ) (m : ℕ) : (projective u m).natDegree ≤ 2*m+1 := by
  induction m with
  | zero =>
    unfold projective
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_monomial_le (m := 0) (1+u)).trans (by decide)
    · exact natDegree_monomial_le (m := 1) (2 : ℝ)
  | succ m ih =>
    change (step 1 ((m : ℝ)+3) (step (1+u) ((m : ℝ)+3) (projective u m))).natDegree ≤ _
    have ha := step_degree_le (1+u) ((m : ℝ)+3) (projective u m)
    have hb := step_degree_le 1 ((m : ℝ)+3) (step (1+u) ((m : ℝ)+3) (projective u m))
    omega

/-- Numerator for source rank m+1, including the zero at the origin. -/
noncomputable def sourceNumerator (u : ℝ) (m : ℕ) : ℝ[X] :=
  X * inverse (2*m+1) (projective u m)

theorem sourceNumerator_two (u : ℝ) : sourceNumerator u 1 = secondNumerator u := by
  apply Polynomial.eq_of_infinite_eval_eq
  let f : ℕ → ℝ := fun n => -(n : ℝ)
  have hinj : Function.Injective f := fun _ _ h => Nat.cast_injective (neg_injective h)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n,rfl⟩
  have hn : (0 : ℝ) ≤ n := by positivity
  have hx' : f n ≠ 1 := by dsimp [f]; linarith
  change (X * inverse 3 (projective u 1)).eval (f n) = _
  rw [eval_mul, eval_X, inverse_eval (projective_degree_le u 1) hx',
    secondNumerator_eval, projective_second_eval]
  unfold f2
  field_simp [sub_ne_zero.mpr hx'.symm]
  ring

private theorem projective_first_splits (u : ℝ) : (projective u 0).Splits := by
  apply Splits.of_natDegree_le_one
  exact projective_degree_le u 0

theorem sourceNumerator_splits_iff_rank_two {u : ℝ} (hu : 0 ≤ u) :
    (∀ m : ℕ, (sourceNumerator u m).Splits) ↔ (secondNumerator u).Splits := by
  constructor
  · intro h
    simpa [sourceNumerator_two] using h 1
  · intro h
    obtain ⟨l, hl, r, hr, _, _, hcut⟩ := secondNumerator_splits_sharp
    have hur := ((hcut u).mp h).2
    have h₃ : u < 3 := hur.trans_lt (hr.2.trans (by norm_num))
    have hdisc := (factors_iff_disc u).mp ((splits_iff_factors u).mp h)
    intro m
    have hp : (projective u m).Splits := by
      cases m with
      | zero => exact projective_first_splits u
      | succ k => exact (projective_splits_for_cutoff hu h₃ hdisc k).1
    exact Splits.X.mul (inverse_splits hp (projective_degree_le u m))

theorem sharp_nonnegative_numerator_interval :
    ∃ ρ ∈ Set.Ioo (41/20 : ℝ) (33/16), disc ρ = 0 ∧
      ∀ u : ℝ, 0 ≤ u → ((∀ m : ℕ, (sourceNumerator u m).Splits) ↔ u ≤ ρ) := by
  obtain ⟨l, hl, r, hr, _, hdr, hcut⟩ := secondNumerator_splits_sharp
  refine ⟨r, hr, hdr, fun u hu => ?_⟩
  rw [sourceNumerator_splits_iff_rank_two hu, hcut]
  have hneg : l < 0 := hl.2.trans (by norm_num)
  exact and_iff_right (hneg.le.trans hu)

end JacobiProjective
