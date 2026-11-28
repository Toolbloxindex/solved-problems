import JacobiCofactors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace JacobiProjective

open Polynomial
open scoped BigOperators

private noncomputable def augmented (p : ℝ[X]) : ℝ[X] := X*(1+X)*p

private theorem augmented_eq_factors (p : ℝ[X]) :
    augmented p = (X-C 0)*(X-C (-1))*p := by
  simp [augmented, sub_eq_add_neg, add_comm]

private theorem augmented_ne_zero {p : ℝ[X]} (hp : p ≠ 0) : augmented p ≠ 0 := by
  rw [augmented_eq_factors]
  exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) hp

private theorem augmented_splits {p : ℝ[X]} (hp : p.Splits) : (augmented p).Splits := by
  rw [augmented_eq_factors]
  exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).mul hp

private theorem augmented_roots {p : ℝ[X]} (hp : p ≠ 0) :
    (augmented p).roots = ({0, -1} : Multiset ℝ) + p.roots := by
  rw [augmented_eq_factors,
    roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) hp),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
  rfl

private theorem step_eval_eq_augmented_derivative (a b x : ℝ) (p : ℝ[X]) :
    (step a b p).eval x =
      (augmented p).derivative.eval x + ((a-1)*(1+x)+(b-a-1)*x)*p.eval x := by
  simp [step, augmented, derivative_mul]
  ring

private noncomputable def poleWeights (a b : ℝ) (F : ℝ[X]) (r : ℝ) : ℝ := by
  classical
  exact (F.roots.count r : ℝ) + (if r=0 then a-1 else 0) +
    (if r= -1 then b-a-1 else 0)

private theorem poleWeights_pos {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (F : ℝ[X]) {r : ℝ} (hr : r ∈ F.roots.toFinset) :
    0 < poleWeights a b F r := by
  classical
  have hn : (1 : ℝ) ≤ (F.roots.count r : ℝ) := by
    exact_mod_cast (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hr))
  by_cases h₀ : r = 0
  · have h₁ : r ≠ -1 := by rw [h₀]; norm_num
    simp only [poleWeights, ite_eq_left h₀, ite_eq_right h₁, add_zero]
    linarith
  · by_cases h₁ : r = -1
    · simp only [poleWeights, ite_eq_right h₀, ite_eq_left h₁, add_zero]
      linarith
    · simp only [poleWeights, ite_eq_right h₀, ite_eq_right h₁, add_zero]
      linarith

private theorem weighted_reciprocal_sum (a b : ℝ) (F : ℝ[X]) (x : ℝ)
    (h₀ : (0 : ℝ) ∈ F.roots.toFinset) (h₁ : (-1 : ℝ) ∈ F.roots.toFinset) :
    ∑ r ∈ F.roots.toFinset, poleWeights a b F r/(x-r) =
      (F.roots.map fun r => 1/(x-r)).sum + (a-1)/x+(b-a-1)/(1+x) := by
  classical
  simp only [poleWeights, add_div, Finset.sum_add_distrib, ite_div, zero_div]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left h₀, ite_eq_left h₁]
  simp only [sub_zero, sub_neg_eq_add, add_comm x 1]
  congr 2
  rw [Finset.sum_multiset_map_count]
  exact Finset.sum_congr rfl fun r _ => by simp [nsmul_eq_mul, div_eq_mul_inv]

private noncomputable def retainedRoots (F : ℝ[X]) : Multiset ℝ := by
  classical
  exact F.roots - F.roots.toFinset.val

private theorem retainedRoots_add_nodes (F : ℝ[X]) :
    retainedRoots F + F.roots.toFinset.val = F.roots := by
  classical
  exact tsub_add_cancel_of_le (Multiset.dedup_le _)

private noncomputable def retained (F : ℝ[X]) : ℝ[X] :=
  C F.leadingCoeff * ((retainedRoots F).map (X-C ·)).prod

private theorem retained_mul_nodeProduct {F : ℝ[X]} (hF : F.Splits) :
    retained F * nodeProduct F.roots.toFinset = F := by
  rw [retained, nodeProduct, Finset.prod, mul_assoc, ← Multiset.prod_add, ← Multiset.map_add,
    retainedRoots_add_nodes, ← hF.eq_prod_roots]

private theorem step_eq_retained_mul (a b : ℝ) {p : ℝ[X]}
    (hp : p ≠ 0) (hps : p.Splits) :
    step a b p = retained (augmented p) *
      cofactorSum (augmented p).roots.toFinset (poleWeights a b (augmented p)) := by
  classical
  let F := augmented p
  let s := F.roots.toFinset
  let Q := nodeProduct s
  let W := cofactorSum s (poleWeights a b F)
  have hF := augmented_ne_zero hp
  have hFs := augmented_splits hps
  have h0 : (0 : ℝ) ∈ s := by simp [s, F, augmented_roots hp]
  have h1 : (-1 : ℝ) ∈ s := by simp [s, F, augmented_roots hp]
  have hid : Q*step a b p = F*W := by
    apply Polynomial.funext
    intro x
    simp only [eval_mul]
    by_cases hx : x ∈ s
    · have hfx : F.eval x = 0 :=
        (mem_roots hF).mp (Multiset.mem_toFinset.mp hx)
      have hqx : Q.eval x = 0 := by
        rw [show Q = nodeProduct s from rfl, nodeProduct_eval, ← Finset.mul_prod_erase _ _ hx]
        simp
      rw [hfx,hqx,zero_mul,zero_mul]
    · have hfx : F.eval x ≠ 0 := by
        intro hx'
        exact hx (Multiset.mem_toFinset.mpr ((mem_roots hF).mpr hx'))
      have hx0 : x ≠ 0 := fun h => hx (h ▸ h0)
      have hx1 : 1+x ≠ 0 := by
        intro h
        have h' : x = -1 := by linarith
        exact hx (h' ▸ h1)
      have hFe : F.eval x = x*(1+x)*p.eval x := by simp [F, augmented]
      have hder := hFs.eval_derivative_eq_eval_mul_sum hfx
      rw [show W = cofactorSum s (poleWeights a b F) from rfl,
        cofactorSum_eval_off_nodes s _ hx, weighted_reciprocal_sum a b F x h0 h1,
        step_eval_eq_augmented_derivative]
      change Q.eval x *
        (F.derivative.eval x + ((a-1)*(1+x)+(b-a-1)*x)*p.eval x) = _
      rw [hder, hFe]
      field_simp
      ring
  have hQ : Q ≠ 0 := (monic_prod_X_sub_C id s).ne_zero
  apply mul_left_cancel₀ hQ
  calc
    Q * step a b p = F * W := hid
    _ = Q * (retained F * W) := by
      have hfac : retained F * Q = F := retained_mul_nodeProduct hFs
      calc
        F * W = (retained F * Q) * W := congrArg (fun z => z * W) hfac.symm
        _ = _ := by ring

/-- The first-order projective operator preserves splitting with all roots negative.
Repeated input roots are retained with their exact product multiplicities. -/
theorem step_splits_negative {a b : ℝ} {p : ℝ[X]} (ha : 0 < a) (hab : a < b)
    (hp : p.Splits) (hneg : ∀ r ∈ p.roots, r < 0) :
    (step a b p).Splits ∧ ∀ r ∈ (step a b p).roots, r < 0 := by
  classical
  by_cases hp₀ : p = 0
  · simp [step, hp₀]
  let F := augmented p
  let s := F.roots.toFinset
  let W := cofactorSum s (poleWeights a b F)
  have h0 : (0 : ℝ) ∈ s := by simp [s, F, augmented_roots hp₀]
  have hs : ∀ r ∈ s, r ≤ 0 := by
    intro r hr
    have hm : r ∈ F.roots := Multiset.mem_toFinset.mp hr
    rw [show F = augmented p from rfl, augmented_roots hp₀, Multiset.mem_add] at hm
    rcases hm with hm | hm
    · simp at hm
      rcases hm with rfl | rfl <;> norm_num
    · exact (hneg r hm).le
  obtain ⟨hWs, hWneg⟩ := cofactorSum_splits_and_roots_lt s (poleWeights a b F)
    ⟨0,h0⟩ (fun _ hr => poleWeights_pos ha hab F hr) hs
  have hre : step a b p = retained F * W := step_eq_retained_mul a b hp₀ hp
  have hE : (retained F).Splits := by
    unfold retained
    apply (Splits.C _).mul
    apply Splits.multisetProd
    intro q hq
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hq
    exact Splits.X_sub_C r
  rw [hre]
  refine ⟨hE.mul hWs, ?_⟩
  by_cases hE₀ : retained F = 0
  · simp [hE₀]
  by_cases hW₀ : W = 0
  · simp [hW₀]
  rw [roots_mul (mul_ne_zero hE₀ hW₀)]
  have hC : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (augmented_ne_zero hp₀)
  intro r hr
  rcases Multiset.mem_add.mp hr with hr | hr
  · have hret : (retained F).roots = retainedRoots F := by
      unfold retained
      rw [roots_C_mul _ hC, roots_multiset_prod_X_sub_C]
    rw [hret] at hr
    have hrF : r ∈ F.roots := Multiset.mem_of_le tsub_le_self hr
    have hle := hs r (Multiset.mem_toFinset.mpr hrF)
    refine lt_of_le_of_ne hle ?_
    rintro rfl
    have hcount : F.roots.count 0 = 1 := by
      rw [show F = augmented p from rfl, augmented_roots hp₀, Multiset.count_add]
      have hnone : (0 : ℝ) ∉ p.roots := fun h => lt_irrefl _ (hneg _ h)
      simp [Multiset.count_eq_zero_of_notMem hnone]
    have hc := congrArg (Multiset.count (0 : ℝ)) (retainedRoots_add_nodes F)
    rw [Multiset.count_add, hcount] at hc
    have hh : 0 < F.roots.toFinset.val.count 0 :=
      Multiset.count_pos.mpr (Finset.mem_val.mpr h0)
    have ht : 0 < (retainedRoots F).count 0 := Multiset.count_pos.mpr hr
    omega
  · exact hWneg r hr

end JacobiProjective
