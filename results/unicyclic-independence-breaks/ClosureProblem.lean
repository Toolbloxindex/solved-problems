import GraphSource
import GraphDigits

namespace UnicyclicClosure

namespace Build

def size : Build → ℕ
  | .node => 1
  | .attach L R => L.size + R.size
  | .markedArms => 5

theorem cardV (B : Build) : Fintype.card B.V = B.size := by
  induction B with
  | node => decide
  | attach L R hL hR =>
    change Fintype.card (L.V ⊕ R.V) = L.size + R.size
    rw [Fintype.card_sum, hL, hR]
  | markedArms => decide

/-- Conditional evaluations with the root excluded and included. -/
def values (x : ℕ) (close : Bool) : Build → ℕ × ℕ
  | .node => (Rooted.node.eval x false, Rooted.node.eval x true)
  | .attach L R =>
    let (outL, inL) := L.values x close
    let (outR, inR) := R.values x close
    (outL * (outR + inR), inL * outR)
  | .markedArms => ((marked close).eval x false, (marked close).eval x true)

theorem values_correct (B : Build) (x : ℕ) (close : Bool) :
    B.values x close = ((B.rooted close).eval x false, (B.rooted close).eval x true) := by
  induction B with
  | node => rfl
  | markedArms => rfl
  | attach L R hL hR =>
    simp only [values, hL, hR]
    refine Prod.ext ?_ ?_
    · exact (Rooted.eval_attach (L.rooted close) (R.rooted close) x false).symm
    · exact (Rooted.eval_attach (L.rooted close) (R.rooted close) x true).symm

def base (B : Build) : ℕ := 2 ^ (B.size + 1)

def packedValue (B : Build) : ℕ :=
  let p := B.values B.base true
  p.1 + p.2

def extracted (B : Build) (k : ℕ) : ℕ := digit B.base B.packedValue k

theorem count_extracted (B : Build) (k : ℕ) (hk : k ≤ B.size) :
    (B.rooted true).count k = B.extracted k := by
  have hb : 2 ^ Fintype.card B.V < B.base := by
    rw [cardV, base, pow_succ]
    have hpos := Nat.two_pow_pos B.size
    omega
  rw [Rooted.count_eq_digit _ _ _ hb (by rwa [cardV]), extracted, packedValue, values_correct]

end Build

def Unimodal (c : ℕ → ℕ) : Prop :=
  ∃ p, (∀ k < p, c k ≤ c (k + 1)) ∧ (∀ k, p ≤ k → c (k + 1) ≤ c k)

def BreakAt (c : ℕ → ℕ) (k : ℕ) : Prop :=
  0 < k ∧ c k ^ 2 < c (k - 1) * c (k + 1)

instance (c : ℕ → ℕ) (k : ℕ) : Decidable (BreakAt c k) := by
  unfold BreakAt
  infer_instance

/-- Check consecutive digits in a single pass. -/
def checkPeak (base : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | rem + 1, p, n =>
    let q := n / base
    let lo := n % base
    let hi := q % base
    (if p = 0 then decide (hi ≤ lo) else decide (lo ≤ hi)) &&
      checkPeak base rem (p - 1) q

theorem digit_div (base n k : ℕ) :
    digit base (n / base) k = digit base n (k + 1) := by
  simp only [digit, pow_succ', Nat.div_div_eq_div_mul]

theorem checkPeak_correct (base steps p n : ℕ) (h : checkPeak base steps p n = true)
    (k : ℕ) (hk : k < steps) :
    if k < p then digit base n k ≤ digit base n (k + 1)
    else digit base n (k + 1) ≤ digit base n k := by
  induction steps generalizing p n k with
  | zero => omega
  | succ rem ih =>
    simp only [checkPeak, Bool.and_eq_true] at h
    cases k with
    | zero =>
      by_cases hp : p = 0
      · simp only [hp, ite_true, decide_eq_true_eq] at h
        simpa [hp, digit] using h.1
      · have hp' : 0 < p := Nat.pos_of_ne_zero hp
        simp only [hp, ite_false, decide_eq_true_eq] at h
        simpa [hp', digit] using h.1
    | succ k =>
      have hh := ih (p - 1) (n / base) h.2 k (by omega)
      have hc : k < p - 1 ↔ k + 1 < p := by omega
      simpa only [digit_div, hc] using hh

namespace Build

theorem unimodal_of_check (B : Build) (p : ℕ) (hp : p ≤ B.size)
    (hc : checkPeak B.base B.size p B.packedValue = true) :
    Unimodal (B.rooted true).count := by
  refine ⟨p, ?_, ?_⟩
  · intro k hk
    have hh := checkPeak_correct _ _ _ _ hc k (by omega)
    rw [ite_eq_left hk] at hh
    rw [count_extracted B k (by omega), count_extracted B (k + 1) (by omega)]
    exact hh
  · intro k hk
    by_cases hv : k < B.size
    · have hh := checkPeak_correct _ _ _ _ hc k hv
      rw [ite_eq_right (by omega)] at hh
      rw [count_extracted B k (by omega), count_extracted B (k + 1) (by omega)]
      exact hh
    · rw [Rooted.count_eq_zero _ _ (by rw [cardV]; omega)]
      exact Nat.zero_le _

theorem break_of_check (B : Build) (k : ℕ) (hk : k + 1 ≤ B.size)
    (h : BreakAt B.extracted k) : BreakAt (B.rooted true).count k := by
  simpa only [BreakAt, count_extracted B k (by omega), count_extracted B (k - 1) (by omega),
    count_extracted B (k + 1) hk] using h

/-- A member of the source tree family, its one-edge enlargement, and the
specified violations of log-concavity in the independent-set sequence. -/
def GoodClosure (B : Build) (indices : List ℕ) : Prop :=
  (B.rooted false).graph.IsTree ∧
    (∃ u v : B.V, u ≠ v ∧ ¬(B.rooted false).graph.Adj u v ∧
      (B.rooted true).graph = (B.rooted false).graph ⊔ SimpleGraph.edge u v) ∧
    Unimodal (B.rooted true).count ∧
    ∀ k ∈ indices, BreakAt (B.rooted true).count k

theorem goodClosure_of_checks (B : Build) (indices : List ℕ) (p : ℕ)
    (hm : B.marks = 1) (hp : p ≤ B.size)
    (hc : checkPeak B.base B.size p B.packedValue = true)
    (hb : ∀ k ∈ indices, k + 1 ≤ B.size ∧ BreakAt B.extracted k) :
    B.GoodClosure indices := by
  obtain ⟨u,v, hne, hn, he⟩ := B.closes_one_edge hm
  refine ⟨B.isTree_unclosed, ⟨u, v, hne, hn, congrArg Rooted.graph he⟩,
    B.unimodal_of_check p hp hc, ?_⟩
  intro k hk
  exact B.break_of_check k (hb k hk).1 (hb k hk).2

end Build

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
open Build in
theorem problem_6_6 :
    TG25.GoodClosure [34, 36] ∧
    patternTwo16.GoodClosure [162, 163] ∧
    patternThree13.GoodClosure [161, 162, 163] := by
  refine ⟨goodClosure_of_checks _ _ 21 (by decide) (by decide) ?_ ?_,
    goodClosure_of_checks _ _ 95 (by decide) (by decide) ?_ ?_,
    goodClosure_of_checks _ _ 97 (by decide) (by decide) ?_ ?_⟩
  · decide
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    decide
  · decide
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    decide
  · decide
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    decide

#print axioms problem_6_6

end UnicyclicClosure
