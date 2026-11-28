module

public import GraphCount

@[expose] public section

open scoped BigOperators

namespace UnicyclicClosure

/-- There are no carries when the digits are less than the base. -/
def encode (base : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => a 0 + base * encode base (fun k => a (k + 1)) n

/-- Read the coefficient of degree `k` from the encoded natural number. -/
def digit (base value k : ℕ) : ℕ := value / base ^ k % base

theorem encode_eq_sum (base : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    encode base a n = ∑ k ∈ Finset.range n, base ^ k * a k := by
  induction n generalizing a with
  | zero => simp [encode]
  | succ n ih =>
    simp only [encode, ih, Finset.sum_range_succ', pow_zero, one_mul, pow_succ',
      mul_assoc, ← Finset.mul_sum]
    omega

theorem digit_encode (base n k : ℕ) (a : ℕ → ℕ) (hb : 0 < base)
    (ha : ∀ j, a j < base) (hk : k < n) :
    digit base (encode base a n) k = a k := by
  induction n generalizing a k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      simp [digit, encode, Nat.add_mod, Nat.mod_eq_of_lt (ha 0)]
    | succ k =>
      have hh := ih k (fun j => a (j + 1)) (fun j => ha (j + 1)) (by omega)
      have step : (a 0 + base * encode base (fun j => a (j + 1)) n) / base =
          encode base (fun j => a (j + 1)) n := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (ha 0), zero_add]
      simpa only [digit, encode, pow_succ', ← Nat.div_div_eq_div_mul, step] using hh

namespace Rooted

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : Rooted V) [DecidableRel G.graph.Adj]

/-- Exact independent-set count from the graph, at the indicated size. -/
def count (k : ℕ) : ℕ := (G.graph.indepSetFinset k).card

theorem count_le (k : ℕ) : G.count k ≤ 2 ^ Fintype.card V := by
  rw [count, ← Fintype.card_finset, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

theorem count_eq_zero (k : ℕ) (hk : Fintype.card V < k) : G.count k = 0 := by
  rw [count, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hc : s.card ≤ Fintype.card V := Finset.card_le_univ s
  have hrs := (G.graph.isNIndepSet_iff k s).mp (SimpleGraph.mem_indepSetFinset_iff.mp hs)
  omega

theorem sum_count (k : ℕ) :
    (∑ s : Finset V, if G.graph.IsIndepSet s ∧ s.card = k then 1 else 0) = G.count k := by
  simp [count, SimpleGraph.indepSetFinset, SimpleGraph.isNIndepSet_iff]

theorem eval_encode (base : ℕ) :
    G.eval base false + G.eval base true =
      encode base G.count (Fintype.card V + 1) := by
  rw [eval, eval, ← Finset.sum_add_distrib, encode_eq_sum]
  calc
    _ = ∑ s : Finset V, ∑ k ∈ Finset.range (Fintype.card V + 1),
        if G.graph.IsIndepSet s ∧ s.card = k then base ^ k else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          have hcard : s.card ≤ Fintype.card V := Finset.card_le_univ s
          have hm : s.card ∈ Finset.range (Fintype.card V + 1) := by
            rw [Finset.mem_range]
            omega
          rw [Finset.sum_eq_single_of_mem s.card hm]
          · by_cases h : G.root ∈ s <;> simp [h]
          · intro k _ hk
            simp [Ne.symm hk]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← G.sum_count, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      split <;> simp_all

theorem count_eq_digit (base k : ℕ) (hb : 2 ^ Fintype.card V < base)
    (hk : k ≤ Fintype.card V) :
    G.count k = digit base (G.eval base false + G.eval base true) k := by
  rw [G.eval_encode, digit_encode]
  · exact lt_of_le_of_lt (Nat.zero_le _) hb
  · exact fun j => lt_of_le_of_lt (G.count_le j) hb
  · omega

end Rooted
end UnicyclicClosure
