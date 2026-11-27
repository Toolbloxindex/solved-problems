import Std
namespace FirstColumn

/-- Coefficients of F₀ = 0 and Fₙ₊₁ = 1 + (1+q+q²)Fₙ, including
zero extension to all integer degrees. -/
def f : Nat → Int → Int
  | 0, _ => 0
  | n+1, d => f n d + f n (d-1) + f n (d-2) + (if d=0 then 1 else 0)

theorem nonneg (n : Nat) (d : Int) : 0 ≤ f n d := by
  induction n generalizing d with
  | zero => change (0:Int) ≤ 0; decide
  | succ n ih =>
    have h0 := ih d
    have h1 := ih (d-1)
    have h2 := ih (d-2)
    simp only [f]
    split <;> omega

theorem off_left (n : Nat) (d : Int) (h : d < 0) : f n d = 0 := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp [f, ih d h, ih (d-1) (by omega), ih (d-2) (by omega), Int.ne_of_lt h]

theorem off_right (n : Nat) (d : Int) (h : 2*(n : Int)-2 < d) : f n d = 0 := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp [f, ih d (by omega), ih (d-1) (by omega), ih (d-2) (by omega),
      show d ≠ 0 by omega]

theorem pos_on (n : Nat) (d : Int) (hl : 0 ≤ d) (hr : d ≤ 2*(n : Int)-2) : 0 < f n d := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    have h0 := nonneg n d
    have h1 := nonneg n (d-1)
    have h2 := nonneg n (d-2)
    simp only [f]
    split
    · omega
    · by_cases h : d ≤ 2*(n : Int)-2
      · have := ih d hl h; omega
      · by_cases h' : 2 ≤ d
        · have := ih (d-2) (by omega) (by omega); omega
        · have := ih (d-1) (by omega) (by omega); omega

def Local (a : Int → Int) := ∀ d, a (d-1) * a (d+1) ≤ a d ^ 2

private theorem strongGap (n : Nat) (hlc : Local (f n)) (i : Int) (k : Nat) :
    f n (i-1) * f n (i+(k : Int)+1) ≤ f n i * f n (i+(k : Int)) := by
  induction k with
  | zero => simpa [Int.pow_succ] using hlc i
  | succ k ih =>
    let j := i+(k : Int)+1
    have now : f n (i-1)*f n j ≤ f n i*f n (j-1) := by
      simpa [j] using ih
    have localj := hlc j
    have eqL : i + ((k+1 : Nat) : Int) = j := by dsimp [j]; omega
    rw [eqL]
    by_cases lo : j < 0
    · have hz := off_left n (i-1) (by dsimp [j] at lo; omega)
      rw [hz, off_left n j lo]
      simp
    by_cases hi : 2*(n : Int)-2 < j
    · rw [off_right n (j+1) (by omega), off_right n j hi]
      simp
    have hj := pos_on n j (by omega) (by omega)
    have h1 := Int.mul_le_mul_of_nonneg_right now (nonneg n (j+1))
    have h2 := Int.mul_le_mul_of_nonneg_left localj (nonneg n i)
    have h3 : f n (i-1)*f n (j+1)*f n j ≤ f n i*f n j*f n j := by
      grind only
    exact Int.le_of_mul_le_mul_right h3 hj

private theorem window (n : Nat) (hc : Local (f n)) (d : Int) :
    (f n (d-1)+f n (d-2)+f n (d-3))*(f n (d+1)+f n d+f n (d-1)) ≤
    (f n d+f n (d-1)+f n (d-2))^2 := by
  have a := hc (d-2)
  have b := strongGap n hc (d-2) 1
  have c := strongGap n hc (d-2) 2
  have e := strongGap n hc (d-1) 1
  have g := hc d
  simp only [Int.natCast_succ, Int.natCast_zero] at *
  grind only

theorem low_degrees (n : Nat) : f n 0 = (n : Int) ∧
    2*f n 1 = (n : Int)*((n : Int)-1) ∧
    6*f n 2 = ((n : Int)+1)*(n : Int)*((n : Int)-1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨a,b,c⟩ := ih
    have l1 := off_left n (-1) (by decide)
    have l2 := off_left n (-2) (by decide)
    simp [f,a,l1,l2,Int.natCast_succ] <;> grind only

private theorem gap_one (n : Nat) (hn : 5 ≤ n) : f n 0 * f n 2 ≤ f n 1 ^ 2 := by
  obtain ⟨a,b,c⟩ := low_degrees n
  let x := (n : Int)
  have eq : 12*(f n 1 ^ 2 - f n 0*f n 2) = x^2*(x-1)*(x-5) := by
    calc
      _ = 3*(2*f n 1)^2 - 2*f n 0*(6*f n 2) := by grind only
      _ = _ := by rw [a,b,c]; dsimp [x]; grind only
  have h := Int.mul_nonneg (Int.mul_nonneg (Int.sq_nonneg x)
    (show 0 ≤ x-1 by dsimp [x]; omega)) (show 0 ≤ x-5 by dsimp [x]; omega)
  omega

private theorem base_five : Local (f 5) := by
  intro d
  by_cases l : d ≤ 0
  · rw [off_left 5 (d-1) (by omega), Int.zero_mul]
    exact Int.sq_nonneg _
  by_cases r : 8 ≤ d
  · rw [off_right 5 (d+1) (by omega), Int.mul_zero]
    exact Int.sq_nonneg _
  have cs : d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 := by omega
  rcases cs with h|h|h|h|h|h|h <;> subst d <;> decide

theorem ordinary_from_five (n : Nat) : Local (f (n+5)) := by
  induction n with
  | zero => exact base_five
  | succ n ih =>
    intro d
    by_cases hl : d ≤ 0
    · rw [off_left (n+1+5) (d-1) (by omega), Int.zero_mul]
      exact Int.sq_nonneg _
    by_cases ho : d = 1
    · subst d
      exact gap_one (n+1+5) (by omega)
    have h := window (n+5) ih d
    change f ((n+5)+1) (d-1)*f ((n+5)+1) (d+1) ≤ f ((n+5)+1) d^2
    have step (x : Int) (hx : x ≠ 0) : f ((n+5)+1) x =
        f (n+5) x + f (n+5) (x-1) + f (n+5) (x-2) := by
      change _ + (if x=0 then (1:Int) else 0) = _
      simp [hx]
    rw [step (d-1) (by omega), step (d+1) (by omega), step d (by omega)]
    rw [show d-1-1=d-2 by omega, show d-1-2=d-3 by omega,
      show d+1-1=d by omega, show d+1-2=d-1 by omega]
    exact h

def Parity (a : Int → Int) := ∀ d, a (d-2) * a (d+2) ≤ a d ^ 2

theorem parity_all (n : Nat) : Parity (f n) := by
  intro d
  by_cases large : 5 ≤ n
  · have hc : Local (f n) := by
      have eq : n-5+5 = n := by omega
      simpa only [eq] using ordinary_from_five (n-5)
    have h := strongGap n hc (d-1) 2
    have a := hc d
    grind only
  by_cases hl : d < 2
  · rw [off_left n (d-2) (by omega), Int.zero_mul]
    exact Int.sq_nonneg _
  by_cases hr : 2*(n:Int)-2 < d+2
  · rw [off_right n (d+2) hr, Int.mul_zero]
    exact Int.sq_nonneg _
  have ns : n=3 ∨ n=4 := by omega
  have ds : d=2 ∨ d=3 ∨ d=4 := by omega
  rcases ns with h|h <;> rcases ds with i|i|i <;> subst n <;> subst d <;> decide

theorem ordinary_iff (n : Nat) : Local (f n) ↔ n ≤ 1 ∨ 5 ≤ n := by
  constructor
  · intro lc
    by_cases h : n ≤ 1 ∨ 5 ≤ n
    · exact h
    exfalso
    have ns : n=2 ∨ n=3 ∨ n=4 := by omega
    have hx := lc 1
    rcases ns with h|h|h <;> subst n <;> revert hx <;> decide
  · intro h
    rcases h with small|large
    · intro d
      by_cases l : d ≤ 0
      · rw [off_left n (d-1) (by omega), Int.zero_mul]
        exact Int.sq_nonneg _
      · rw [off_right n (d+1) (by omega), Int.mul_zero]
        exact Int.sq_nonneg _
    · have eq : n-5+5=n := by omega
      simpa only [eq] using ordinary_from_five (n-5)

/-- Convolution with the q-integer [w]. -/
def qmul (a : Int → Int) (d : Int) : Nat → Int
  | 0 => 0
  | w+1 => qmul a d w + a (d-(w:Int))

/-- Coefficients of the second-kind array, Sagan--Swanson Definition 1.5,
for every natural n,k. The omitted k=-1 summand at k=0 is zero. -/
def sb : Nat → Nat → Int → Int
  | 0,k,d => if k=0 ∧ d=0 then 1 else 0
  | n+1,0,d => qmul (sb n 0) d 1
  | n+1,k+1,d => sb n k d + qmul (sb n (k+1)) d (2*(k+1)+1)

theorem column_zero (n : Nat) (d : Int) : sb n 0 d = if d=0 then 1 else 0 := by
  induction n with
  | zero => simp [sb]
  | succ n ih => simpa [sb,qmul] using ih

theorem column_one (n : Nat) (d : Int) : sb n 1 d = f n d := by
  induction n generalizing d with
  | zero => simp [sb,f]
  | succ n ih =>
    simp [sb,qmul,f,column_zero,ih]
    grind only

theorem original_column_parity (n : Nat) : Parity (sb n 1) := by
  have eq : sb n 1 = f n := funext (column_one n)
  rw [eq]
  exact parity_all n

theorem original_column_ordinary_iff (n : Nat) : Local (sb n 1) ↔ n ≤ 1 ∨ 5 ≤ n := by
  have eq : sb n 1 = f n := funext (column_one n)
  rw [eq]
  exact ordinary_iff n

theorem original_column_positive (n : Nat) (d : Int) (hl : 0 ≤ d) (hr : d ≤ 2*(n:Int)-2) :
    0 < sb n 1 d := by rw [column_one]; exact pos_on n d hl hr

#print axioms FirstColumn.original_column_parity
#print axioms FirstColumn.original_column_ordinary_iff
#print axioms FirstColumn.original_column_positive
end FirstColumn
