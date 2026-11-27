module

public import FirstColumn
public import PairBridge
public import StirlingDiagonal

@[expose] public section

/-! The type B coefficient recurrences of Sagan and Swanson, Definition 1.5
(12), (14), restricted only in the final theorems to n-k = 1 or 2. -/
namespace StirlingRecurrence

open FirstColumn (qmul sb)
open SecondDiagonal (oddInteger productCoeff symmetricTwo)

/-- The signless first kind, with [2n+1] on passing from row n to n+1. -/
def cb : Nat → Nat → Int → Int
  | 0, k, d => if k = 0 ∧ d = 0 then 1 else 0
  | n+1, 0, d => qmul (cb n 0) d (2*n+1)
  | n+1, k+1, d => cb n k d + qmul (cb n (k+1)) d (2*n+1)

/-- True selects (14); false selects the previously defined recurrence (12). -/
def coeff (first : Bool) := if first then cb else sb

def unitCoeff (d : Int) : Int := if d=0 then 1 else 0

private theorem step (e : Bool) (n k : Nat) (d : Int) :
    coeff e (n+1) (k+1) d = coeff e n k d +
      qmul (coeff e n (k+1)) d (2*(if e then n else k+1)+1) := by
  cases e <;> rfl

private theorem step_zero (e : Bool) (n : Nat) (d : Int) :
    coeff e (n+1) 0 d = qmul (coeff e n 0) d (2*(if e then n else 0)+1) := by
  cases e <;> rfl

private theorem mul_zero (w : Nat) (d : Int) : qmul (fun _ => 0) d w = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [qmul, ih]

private theorem above (e : Bool) (n k : Nat) (h : n < k) :
    coeff e n k = fun _ => 0 := by
  induction n generalizing k with
  | zero =>
    funext d
    cases e <;> simp [coeff, sb, cb, show k ≠ 0 by omega]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      funext d
      rw [step, ih k (by omega), ih (k+1) (by omega), mul_zero]
      rfl

private theorem diagonal (e : Bool) (n : Nat) : coeff e n n = unitCoeff := by
  induction n with
  | zero =>
    funext d
    cases e <;> simp [coeff, sb, cb, unitCoeff]
  | succ n ih =>
    funext d
    rw [step, ih, above e n (n+1) (by omega), mul_zero, Int.add_zero]

theorem recurrence_diagonal (first : Bool) (n : Nat) :
    coeff first n n = fun d => if d=0 then 1 else 0 := diagonal first n

private theorem mul_unit (w : Nat) (d : Int) :
    qmul unitCoeff d w = if 0 ≤ d ∧ d < (w : Int) then 1 else 0 := by
  induction w with
  | zero => simp [qmul, show ¬(0 ≤ d ∧ d < 0) by omega]
  | succ w ih =>
    rw [qmul, ih]
    unfold unitCoeff
    simp only [Int.natCast_succ]
    by_cases he : d = (w : Int)
    · subst d
      simp <;> omega
    · have hz : d-(w:Int) ≠ 0 := by omega
      have hc : (0 ≤ d ∧ d < (w:Int)+1) ↔ (0 ≤ d ∧ d < (w:Int)) := by omega
      simp [hz, hc]

def singles (m : Nat) (d : Int) : Int :=
  ((List.range m).map (fun i => oddInteger i d)).sum

private theorem singles_step (m : Nat) (d : Int) :
    singles (m+1) d = singles m d + oddInteger m d := by
  simp [singles, List.range_succ]

private theorem first_diagonal_coeff (e : Bool) (k : Nat) :
    coeff e (k+1) k = singles (k+1) := by
  induction k with
  | zero =>
    funext d
    rw [step_zero, diagonal, mul_unit, singles_step]
    cases e <;> simp [singles, oddInteger] <;> split <;> split <;> omega
  | succ k ih =>
    funext d
    rw [step, ih, diagonal, mul_unit]
    rw [singles_step (k+1) d]
    simp only [ite_self, oddInteger]
    congr 1
    split <;> split <;> omega

private theorem mul_add (f g : Int → Int) (w : Nat) (d : Int) :
    qmul (fun z => f z + g z) d w = qmul f d w + qmul g d w := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [qmul, ih]; omega

private theorem mul_odd (i : Nat) (w : Nat) (d : Int) :
    qmul (oddInteger i) d w =
      max 0 (min (w:Int) (d+1) - max 0 (d-2*(i:Int))) := by
  induction w with
  | zero => simp only [qmul, Int.natCast_zero]; omega
  | succ w ih =>
    rw [qmul, ih]
    unfold oddInteger
    split <;> simp only [Int.natCast_succ] <;> omega

private theorem mul_singles (m j : Nat) (d : Int) :
    qmul (singles m) d (2*j+1) =
      ((List.range m).map (fun i => productCoeff i j d)).sum := by
  induction m with
  | zero => exact mul_zero _ _
  | succ m ih =>
    have h : singles (m+1) = (fun z => singles m z + oddInteger m z) :=
      funext (singles_step m)
    rw [h, mul_add, ih, mul_odd, List.range_succ]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Int.add_zero, SecondDiagonal.product_eq_rect]
    unfold SecondDiagonal.rect
    congr 1
    omega

private theorem pairs_step (e : Bool) (j : Nat) (d : Int) :
    symmetricTwo e (j+1) d = symmetricTwo e j d +
      qmul (singles (if e then j else j+1)) d (2*j+1) := by
  rw [SecondDiagonal.symmetricTwo_step, mul_singles]

theorem second_diagonal_coeff (e : Bool) (k : Nat) (d : Int) :
    coeff e (k+2) k d = symmetricTwo e (if e then k+2 else k+1) d := by
  induction k with
  | zero =>
    rw [step_zero, first_diagonal_coeff]
    cases e
    · simpa [symmetricTwo] using (pairs_step false 0 d).symm
    · have base : symmetricTwo true 1 d = 0 := by rw [SecondDiagonal.symmetricTwo_step]; rfl
      simpa [base] using (pairs_step true 1 d).symm
  | succ k ih =>
    rw [step, ih, first_diagonal_coeff]
    cases e
    · exact (pairs_step false (k+1) d).symm
    · exact (pairs_step true (k+2) d).symm

theorem recurrence_second_strict (first : Bool) (n : Nat) (d : Int)
    (hn : 2 ≤ n) (hd : 0 ≤ d) (hs : d+4 ≤ 4*(n:Int)-(if first then 6 else 8)) :
    coeff first n (n-2) d * coeff first n (n-2) (d+4) <
      coeff first n (n-2) (d+2)^2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  simp only [Nat.add_sub_cancel, second_diagonal_coeff]
  exact SecondDiagonal.original_second_strict first (k+2) d hn hd hs

theorem recurrence_second_positive (first : Bool) (n : Nat) (d : Int)
    (hn : 2 ≤ n) (hd : 0 ≤ d) (hs : d ≤ 4*(n:Int)-(if first then 6 else 8)) :
    0 < coeff first n (n-2) d := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  simp only [Nat.add_sub_cancel, second_diagonal_coeff]
  exact SecondDiagonal.original_second_positive first (k+2) d hn hd hs

private theorem singles_nat (m d : Nat) :
    singles m (d : Int) = (StirlingDiagonal.coeff m d : Int) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [singles_step, ih, StirlingDiagonal.coeff]
    simp only [Int.natCast_add, oddInteger]
    congr 1
    split <;> split <;> omega

/-- The sharp first-diagonal parity gap in the two triangular arrays. -/
theorem recurrence_first_gap (first : Bool) (n d : Nat) (hn : 1 ≤ n)
    (hs : d+4 < 2*n-1) :
    coeff first n (n-1) ((d:Int)+2)^2 =
      coeff first n (n-1) d * coeff first n (n-1) ((d:Int)+4) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  simp only [Nat.add_sub_cancel, first_diagonal_coeff]
  have h := congrArg (fun z : Nat => (z : Int)) (StirlingDiagonal.parity_gap (k+1) d hs)
  rw [show (d:Int)+2 = ((d+2 : Nat):Int) by omega,
      show (d:Int)+4 = ((d+4 : Nat):Int) by omega, singles_nat, singles_nat, singles_nat]
  simpa [Int.pow_succ] using h

#check recurrence_second_strict
#check recurrence_second_positive
#check recurrence_first_gap
#print axioms recurrence_second_strict
#print axioms recurrence_second_positive
#print axioms recurrence_first_gap

/-- The full support degree for $0 ≤ k ≤ n$, from the two source recurrences. -/
def degree (first : Bool) (n k : Nat) : Int :=
  if first then (n:Int)*((n:Int)-1) - (k:Int)*((k:Int)-1)
  else 2*(k:Int)*((n:Int)-(k:Int))

def IntervalSupport (f : Int → Int) (D : Int) : Prop :=
  (∀ d, 0 ≤ f d) ∧ (∀ d, 0 ≤ d → d ≤ D → 0 < f d) ∧
    (∀ d, d < 0 ∨ D < d → f d = 0)

private theorem unit_support : IntervalSupport unitCoeff 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro d <;> unfold unitCoeff
  · split <;> omega
  · intro hl hu
    simp [show d=0 by omega]
  · intro h
    simp [show d≠0 by omega]

private theorem slide_support (f : Int → Int) (D : Int) (hD : 0 ≤ D)
    (hf : IntervalSupport f D) (w : Nat) :
    IntervalSupport (fun d => qmul f d (w+1)) (D+(w:Int)) := by
  rcases hf with ⟨nonneg, pos, off⟩
  induction w with
  | zero =>
    simpa [IntervalSupport, qmul] using And.intro nonneg (And.intro pos off)
  | succ w ih =>
    rcases ih with ⟨old_nonneg, old_pos, old_off⟩
    refine ⟨?_, ?_, ?_⟩
    · intro d
      exact Int.add_nonneg (old_nonneg d) (nonneg _)
    · intro d hl hu
      change 0 < qmul f d (w+1) + f (d-((w+1:Nat):Int))
      by_cases hb : d ≤ D+(w:Int)
      · exact Int.add_pos_of_pos_of_nonneg (old_pos d hl hb) (nonneg _)
      · exact Int.add_pos_of_nonneg_of_pos (old_nonneg d) (pos _ (by omega) (by omega))
    · intro d h
      change qmul f d (w+1) + f (d-((w+1:Nat):Int)) = 0
      have ho : qmul f d (w+1) = 0 := old_off d (by omega)
      rw [ho, off _ (by omega), Int.add_zero]

theorem degree_up (e : Bool) (n k : Nat) :
    degree e (n+1) k = degree e n k + (2*(if e then n else k) : Nat) := by
  cases e <;> simp [degree, Int.add_mul] <;> grind only

theorem degree_both (e : Bool) (n k : Nat) :
    degree e (n+1) (k+1) = degree e n k + 2*((n:Int)-(k:Int)) := by
  cases e <;> simp [degree, Int.mul_add, Int.add_mul] <;> grind only

private theorem degree_nonneg (e : Bool) (n k : Nat) (hk : k ≤ n) :
    0 ≤ degree e n k := by
  induction n generalizing k with
  | zero =>
    have : k=0 := by omega
    subst k
    cases e <;> decide
  | succ n ih =>
    by_cases h : k = n+1
    · subst k
      cases e <;> simp [degree]
    · rw [degree_up]
      have := ih k (by omega)
      omega

private theorem full_support (e : Bool) (n k : Nat) (hk : k ≤ n) :
    IntervalSupport (coeff e n k) (degree e n k) := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    rw [diagonal]
    cases e <;> exact unit_support
  | succ n ih =>
    by_cases top : k = n+1
    · subst k
      rw [diagonal]
      have hz : degree e (n+1) (n+1) = 0 := by cases e <;> simp [degree]
      rw [hz]
      exact unit_support
    have hkn : k ≤ n := by omega
    have prod := slide_support (coeff e n k) (degree e n k) (degree_nonneg e n k hkn)
      (ih k hkn) (2*(if e then n else k))
    rw [← degree_up] at prod
    cases k with
    | zero =>
      have heq : coeff e (n+1) 0 = _ := funext (step_zero e n)
      rw [heq]
      exact prod
    | succ k =>
      rcases ih k (by omega) with ⟨lower_nonneg, _, lower_off⟩
      rcases prod with ⟨upper_nonneg, upper_pos, upper_off⟩
      have bound : degree e n k ≤ degree e (n+1) (k+1) := by rw [degree_both]; omega
      refine ⟨?_, ?_, ?_⟩
      · intro d
        rw [step]
        exact Int.add_nonneg (lower_nonneg d) (upper_nonneg d)
      · intro d hl hu
        rw [step]
        exact Int.add_pos_of_nonneg_of_pos (lower_nonneg d) (upper_pos d hl hu)
      · intro d hd
        rw [step, lower_off d (by omega), Int.zero_add]
        exact upper_off d hd

/-- Exact support and positivity for every nonzero row of both types. -/
theorem recurrence_support (first : Bool) (n k : Nat) (hk : k ≤ n) (d : Int) :
    (0 < coeff first n k d ↔ 0 ≤ d ∧ d ≤ degree first n k) ∧
    (coeff first n k d = 0 ↔ d < 0 ∨ degree first n k < d) := by
  rcases full_support first n k hk with ⟨_, pos, off⟩
  constructor
  · constructor
    · intro h
      by_cases hb : 0 ≤ d ∧ d ≤ degree first n k
      · exact hb
      · have := off d (by omega)
        omega
    · rintro ⟨hl, hu⟩
      exact pos d hl hu
  · constructor
    · intro h
      by_cases hb : d < 0 ∨ degree first n k < d
      · exact hb
      · have := pos d (by omega) (by omega)
        omega
    · exact off d

/-- The conjectured weak parity inequalities, including all zero-extended
endpoints, directly on the original two recurrences at k=n-2. -/
theorem recurrence_second_parity (first : Bool) (n : Nat) (hn : 2 ≤ n) (d : Int) :
    coeff first n (n-2) d * coeff first n (n-2) (d+4) ≤
      coeff first n (n-2) (d+2)^2 := by
  have deg : degree first n (n-2) = 4*(n:Int)-(if first then 6 else 8) := by
    have hk : ((n-2:Nat):Int)=(n:Int)-2 := by omega
    cases first <;> simp [degree, hk] <;> grind only
  by_cases low : 0 ≤ d
  · by_cases high : d+4 ≤ degree first n (n-2)
    · exact Int.le_of_lt (recurrence_second_strict first n d hn low (by simpa [deg] using high))
    · rw [((recurrence_support first n (n-2) (by omega) (d+4)).2).2 (by omega),
          Int.mul_zero]
      exact Int.sq_nonneg _
  · rw [((recurrence_support first n (n-2) (by omega) d).2).2 (by omega),
        Int.zero_mul]
    exact Int.sq_nonneg _

#check recurrence_support
#check recurrence_second_parity
#print axioms recurrence_support
#print axioms recurrence_second_parity

end StirlingRecurrence
