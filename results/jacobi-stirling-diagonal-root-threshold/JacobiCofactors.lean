import JacobiProjective
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

namespace JacobiProjective

open Polynomial
open scoped BigOperators

noncomputable def nodeProduct (s : Finset ℝ) : ℝ[X] :=
  ∏ r ∈ s, (X - C r)

/-- The numerator of a sum of simple fractions with the given nodes. -/
noncomputable def cofactorSum (s : Finset ℝ) (weights : ℝ → ℝ) : ℝ[X] := by
  classical
  exact ∑ r ∈ s, C (weights r) * nodeProduct (s.erase r)

theorem nodeProduct_eval (s : Finset ℝ) (x : ℝ) :
    (nodeProduct s).eval x = ∏ r ∈ s, (x-r) := by
  simp [nodeProduct, eval_prod]

theorem cofactorSum_at_node (s : Finset ℝ) (weights : ℝ → ℝ) {r : ℝ} (hr : r ∈ s) :
    (cofactorSum s weights).eval r =
      weights r * ∏ q ∈ s.erase r, (r-q) := by
  classical
  unfold cofactorSum
  change evalRingHom r _ = _
  rw [map_sum]
  simp only [coe_evalRingHom, eval_mul, eval_C, nodeProduct_eval]
  apply Finset.sum_eq_single_of_mem r hr
  intro q _ hqr
  have hh : r ∈ s.erase q := Finset.mem_erase.mpr ⟨Ne.symm hqr,hr⟩
  rw [← Finset.mul_prod_erase _ _ hh, sub_self, zero_mul, mul_zero]

theorem adjacent_cofactor_signs (s : Finset ℝ) (weights : ℝ → ℝ)
    {r t : ℝ} (hr : r ∈ s) (ht : t ∈ s) (hrt : r < t)
    (hw : ∀ q ∈ s, 0 < weights q)
    (hgap : ∀ q ∈ s, q ≤ r ∨ t ≤ q) :
    (cofactorSum s weights).eval r * (cofactorSum s weights).eval t < 0 := by
  classical
  have hr' : r ∈ s.erase t := Finset.mem_erase.mpr ⟨hrt.ne,hr⟩
  have ht' : t ∈ s.erase r := Finset.mem_erase.mpr ⟨hrt.ne',ht⟩
  rw [cofactorSum_at_node s weights hr, cofactorSum_at_node s weights ht]
  have hs : (s.erase t).erase r = (s.erase r).erase t := by
    ext q
    simp only [Finset.mem_erase]
    exact and_left_comm
  rw [← Finset.mul_prod_erase _ _ ht', ← Finset.mul_prod_erase _ _ hr', hs]
  let rem := (s.erase r).erase t
  change
    (weights r * ((r-t) * ∏ q ∈ rem, (r-q))) *
      (weights t * ((t-r) * ∏ q ∈ rem, (t-q))) < 0
  have hprod : 0 < ∏ q ∈ rem, (r-q)*(t-q) := by
    apply Finset.prod_pos
    intro q hq
    have htq := Finset.mem_erase.mp hq
    have hrq := Finset.mem_erase.mp htq.2
    rcases hgap q hrq.2 with h | h
    · have hq' := lt_of_le_of_ne h hrq.1
      exact mul_pos (sub_pos.mpr hq') (sub_pos.mpr (hq'.trans hrt))
    · have hq' := lt_of_le_of_ne h htq.1.symm
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hrt.trans hq')) (sub_neg.mpr hq')
  rw [Finset.prod_mul_distrib] at hprod
  have heq :
      (weights r * ((r-t) * ∏ q ∈ rem, (r-q))) *
        (weights t * ((t-r) * ∏ q ∈ rem, (t-q))) =
      (r-t) * ((t-r) * ((weights r * weights t) *
        ((∏ q ∈ rem, (r-q)) * (∏ q ∈ rem, (t-q))))) := by ring
  rw [heq]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hrt)
    (mul_pos (sub_pos.mpr hrt) (mul_pos (mul_pos (hw r hr) (hw t ht)) hprod))

theorem cofactorSum_degree_le (s : Finset ℝ) (weights : ℝ → ℝ) :
    (cofactorSum s weights).natDegree ≤ s.card-1 := by
  classical
  unfold cofactorSum
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  have h := Polynomial.natDegree_mul_le
    (p := C (weights r)) (q := nodeProduct (s.erase r))
  simp only [natDegree_C, zero_add] at h
  exact h.trans (by
    unfold nodeProduct
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem hr])

theorem cofactorSum_eval_off_nodes (s : Finset ℝ) (weights : ℝ → ℝ) {x : ℝ}
    (hx : x ∉ s) :
    (cofactorSum s weights).eval x =
      (nodeProduct s).eval x * ∑ r ∈ s, weights r/(x-r) := by
  classical
  unfold cofactorSum
  change evalRingHom x _ = _
  rw [map_sum, Finset.mul_sum]
  simp only [coe_evalRingHom, eval_mul, eval_C, nodeProduct_eval]
  apply Finset.sum_congr rfl
  intro r hr
  have hne : x-r ≠ 0 := sub_ne_zero.mpr (fun h => hx (h ▸ hr))
  rw [← Finset.mul_prod_erase _ _ hr]
  field_simp

/-- Positive weighted cofactors have one new root in every open node gap. -/
theorem cofactorSum_splits_and_roots_lt (s : Finset ℝ) (weights : ℝ → ℝ)
    (hs : s.Nonempty) (hw : ∀ r ∈ s, 0 < weights r)
    {bound : ℝ} (hbound : ∀ r ∈ s, r ≤ bound) :
    (cofactorSum s weights).Splits ∧
      ∀ r ∈ (cofactorSum s weights).roots, r < bound := by
  let n := s.card-1
  have hn : s.card = n+1 := by
    dsimp [n]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm
  let pts := s.orderEmbOfFin hn
  refine splits_and_roots_lt_of_alternating_values (cofactorSum_degree_le s weights)
    pts pts.strictMono ?_ (fun i => hbound _ (s.orderEmbOfFin_mem hn i))
  intro i
  refine adjacent_cofactor_signs s weights
    (s.orderEmbOfFin_mem hn _) (s.orderEmbOfFin_mem hn _) (pts.strictMono i.castSucc_lt_succ) hw ?_
  intro r hr
  have hrep : r ∈ Set.range pts := by simpa [pts, s.range_orderEmbOfFin hn] using hr
  obtain ⟨j,rfl⟩ := hrep
  rcases le_or_gt j i.castSucc with h | h
  · exact Or.inl (pts.monotone h)
  · exact Or.inr (pts.monotone (show i.succ ≤ j from h))

end JacobiProjective
