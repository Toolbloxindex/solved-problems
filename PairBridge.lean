module

public import SecondDiagonal

@[expose] public section

/-! The coefficient of a product of two odd-width q-integers is counted
by its interval of admissible exponent splits. Induction on the larger
factor index identifies those counts with the explicit coefficient formula. -/
namespace SecondDiagonal
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
private def F (d : Int) : Int := max (d+1) 0
private def L (d : Int) : Int := if d < 0 then 0 else (d/2+1)*(d+1-d/2)
private theorem Lstep (d : Int) : L d - L (d-2) = F d := by
  by_cases hn : d < 0
  · simp only [L,hn,show d-2 < 0 by omega,ite_true,F]; omega
  by_cases h : d-2 < 0
  · have : d = 0 ∨ d = 1 := by omega
    rcases this with h|h <;> subst d <;> decide
  have ht : (d-2)/2 = d/2-1 := by omega
  have hf : F d = d+1 := by unfold F; omega
  simp only [L,hn,h,ite_false,ht,hf]
  grind only

/-- Number of integer exponent splits of d between [2i+1] and [2j+1].
The exponents in the first factor form a closed interval of integers. -/
def rect (d i j : Int) := max 0 (min (2*i) d - max 0 (d-2*j) + 1)

private theorem rect_as_ramps (d i j : Int) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    rect d i j = F d - F (d-2*i-1) - F (d-2*j-1) + F (d-2*i-2*j-2) := by
  unfold rect F
  omega

/-- Sum W_i W_j for all i below M at degree d. -/
private def batch : Nat → Int → Int → Int
  | 0, _, _ => 0
  | M+1, j, d => batch M j d + rect d M j

private def increment (M j d : Int) :=
  M * (F d - F (d-2*j-1)) - (L (d-1)-L (d-1-2*M)) +
    (L (d-2*j-2)-L (d-2*j-2-2*M))

private theorem batch_eq (M : Nat) (j d : Int) (hj : 0 ≤ j) :
    batch M j d = increment M j d := by
  induction M with
  | zero => simp [batch,increment]
  | succ M ih =>
    rw [batch,ih,rect_as_ramps _ _ _ (by omega) hj]
    have ha := Lstep (d-1-2*(M:Int))
    have hb := Lstep (d-2*j-2-2*(M:Int))
    have e1 : d-1-2*((M:Int)+1) = d-1-2*(M:Int)-2 := by omega
    have e2 : d-2*j-2-2*((M:Int)+1) = d-2*j-2-2*(M:Int)-2 := by omega
    have e3 : d-2*(M:Int)-1 = d-1-2*(M:Int) := by omega
    have e4 : d-2*(M:Int)-2*j-2 = d-2*j-2-2*(M:Int) := by omega
    simp only [increment,Int.natCast_succ,e1,e2,e3,e4]
    grind only

/-- Sum of coefficients of products W_i W_j with 0 ≤ i < j < m for the
elementary case, or 0 ≤ i ≤ j < m for the complete homogeneous case. -/
def pairCoeff (elem : Bool) : Nat → Int → Int
  | 0, _ => 0
  | j+1, d => pairCoeff elem j d + batch (if elem then j else j+1) j d

private def clipped (e p : Bool) (m t : Int) :=
  if 0 ≤ 2*t+(if p then 1 else 0) ∧ 2*t+(if p then 1 else 0) ≤ 4*m-4-(if e then 2 else 0)
  then coeff24 e p m t else 0

private def bit (p : Bool) : Int := if p then 1 else 0

private theorem Lodd (p : Bool) (z : Int) : L (2*z+bit p-1) =
    (if 0 ≤ z then (z+bit p)*(z+1) else 0) := by
  have ha : (2*z+0-1)/2 = z-1 := by omega
  have hb : (2*z+1-1)/2 = z := by omega
  cases p <;> unfold bit L <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;>
    split <;> split <;> first | omega | (have hz : z=0 := by omega; subst z; decide) | grind only

private theorem Leven (p : Bool) (z : Int) : L (2*z+bit p-2) =
    (if 0 ≤ z then z*(z+bit p) else 0) := by
  have ha : (2*z+0-2)/2 = z-1 := by omega
  have hb : (2*z+1-2)/2 = z-1 := by omega
  cases p <;> unfold bit L <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;>
    split <;> split <;> first | omega | (have hz : z=0 := by omega; subst z; decide) | grind only

private theorem Fshift (p : Bool) (z : Int) : F (2*z+bit p-1) =
    (if 0 ≤ z then 2*z+bit p else 0) := by
  cases p <;> unfold bit F <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> split <;> omega

private theorem norm_increment (p : Bool) (j M t : Int) (ht : 0 ≤ t) :
  increment M j (2*t+bit p) =
   M * (2*t+bit p+1 - (if j ≤ t then 2*(t-j)+bit p else 0)) -
   ((t+bit p)*(t+1) - (if M ≤ t then (t-M+bit p)*(t-M+1) else 0)) +
   ((if j ≤ t then (t-j)*(t-j+bit p) else 0) -
    (if j+M ≤ t then (t-j-M)*(t-j-M+bit p) else 0)) := by
  have hF : F (2*t+bit p)=2*t+bit p+1 := by
    cases p <;> unfold F bit <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> omega
  unfold increment
  rw [hF, show 2*t+bit p-2*j-1=2*(t-j)+bit p-1 by omega, Fshift]
  rw [show 2*t+bit p-1-2*M=2*(t-M)+bit p-1 by omega, Lodd, Lodd]
  rw [show 2*t+bit p-2*j-2=2*(t-j)+bit p-2 by omega,
      show 2*(t-j)+bit p-2-2*M=2*(t-j-M)+bit p-2 by omega, Leven,Leven]
  simp only [show (0 ≤ t-j) ↔ (j ≤ t) by omega,
      show (0 ≤ t-M) ↔ (M ≤ t) by omega,
      show (0 ≤ t-j-M) ↔ (j+M ≤ t) by omega, ht, ite_true]

private theorem norm_clipped (e p : Bool) (m t : Int) (ht : 0 ≤ t) :
    clipped e p m t = if t ≤ 2*m-2-bit e-bit p then
        value e p (decide (m≤t)) m t (t%2) else 0 := by
  unfold clipped coeff24
  have hh : (0 ≤ 2*t+(if p then 1 else 0) ∧
    2*t+(if p then 1 else 0) ≤ 4*m-4-(if e then 2 else 0)) ↔
    t ≤ 2*m-2-bit e-bit p := by cases e <;> cases p <;> simp [bit] <;> omega
  simp only [hh]
private theorem update00 (j t : Int) (hj : 0 ≤ j) (ht : 0 ≤ t) :
    clipped false false (j+1) t - clipped false false j t = 24*increment (j+1) j (2*t+0) := by
  have hn := norm_increment false j (j+1) t ht
  rw [norm_clipped false false (j+1) t ht, norm_clipped false false j t ht]
  simp only [bit, Bool.false_eq_true, ite_true, ite_false] at hn ⊢
  rw [hn]
  clear hn
  by_cases h0 : t ≤ 2*(j+1)-2-0-0
  ·
    by_cases h1 : t ≤ 2*j-2-0-0
    ·
      by_cases h2 : j+1 ≤ t
      ·
        have h3 : j ≤ t := by omega
        have h4 : (j+1) ≤ t := by omega
        have h5 : ¬ j+(j+1) ≤ t := by omega
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
      ·
        by_cases h3 : j ≤ t
        ·
          have h4 : ¬ (j+1) ≤ t := by omega
          have h5 : ¬ j+(j+1) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have htval : t = 1*j+(0) := by omega
          rw [htval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
        ·
          have h4 : ¬ (j+1) ≤ t := by omega
          have h5 : ¬ j+(j+1) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
    ·
      by_cases h2 : j+1 ≤ t
      ·
        have h3 : j ≤ t := by omega
        have h4 : (j+1) ≤ t := by omega
        have h5 : ¬ j+(j+1) ≤ t := by omega
        by_cases hb0 : t ≤ 2*j+(-1)
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2=0 ∨ t%2=1 := by omega
          have htval : t = 2*j+(-1) := by omega
          rw [htval] at hres ⊢
          rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2=0 ∨ t%2=1 := by omega
          have htval : t = 2*j+(0) := by omega
          rw [htval] at hres ⊢
          rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
      ·
        have h3 : j ≤ t := by omega
        have h4 : ¬ (j+1) ≤ t := by omega
        have h5 : ¬ j+(j+1) ≤ t := by omega
        by_cases hb0 : t ≤ 2*j+(-1)
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2=0 ∨ t%2=1 := by omega
          have htval : t = 2*j+(-1) := by omega
          rw [htval] at hres ⊢
          have hjval : j = 1 := by omega
          rw [hjval] at hres ⊢
          rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2=0 ∨ t%2=1 := by omega
          have htval : t = 2*j+(0) := by omega
          rw [htval] at hres ⊢
          have hjval : j = 0 := by omega
          rw [hjval] at hres ⊢
          rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
  ·
    have h1 : ¬ t ≤ 2*j-2-0-0 := by omega
    have h2 : j+1 ≤ t := by omega
    have h3 : j ≤ t := by omega
    have h4 : (j+1) ≤ t := by omega
    have h5 : j+(j+1) ≤ t := by omega
    simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
    clear hj ht h0 h1 h2 h3 h4 h5
    grind only
private theorem update01 (j t : Int) (hj : 0 ≤ j) (ht : 0 ≤ t) :
    clipped false true (j+1) t - clipped false true j t = 24*increment (j+1) j (2*t+1) := by
  have hn := norm_increment true j (j+1) t ht
  rw [norm_clipped false true (j+1) t ht, norm_clipped false true j t ht]
  simp only [bit, Bool.false_eq_true, ite_true, ite_false] at hn ⊢
  rw [hn]
  clear hn
  by_cases h0 : t ≤ 2*(j+1)-2-0-1
  ·
    by_cases h1 : t ≤ 2*j-2-0-1
    ·
      by_cases h2 : j+1 ≤ t
      ·
        have h3 : j ≤ t := by omega
        have h4 : (j+1) ≤ t := by omega
        have h5 : ¬ j+(j+1) ≤ t := by omega
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
      ·
        by_cases h3 : j ≤ t
        ·
          have h4 : ¬ (j+1) ≤ t := by omega
          have h5 : ¬ j+(j+1) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have htval : t = 1*j+(0) := by omega
          rw [htval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
        ·
          have h4 : ¬ (j+1) ≤ t := by omega
          have h5 : ¬ j+(j+1) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
    ·
      by_cases h2 : j+1 ≤ t
      ·
        have h3 : j ≤ t := by omega
        have h4 : (j+1) ≤ t := by omega
        have h5 : ¬ j+(j+1) ≤ t := by omega
        by_cases hb0 : t ≤ 2*j+(-2)
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2 = 0 := by omega
          rw [hres]
          have htval : t = 2*j+(-2) := by omega
          rw [htval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2 = 1 := by omega
          rw [hres]
          have htval : t = 2*j+(-1) := by omega
          rw [htval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
      ·
        by_cases h3 : j ≤ t
        ·
          have h4 : ¬ (j+1) ≤ t := by omega
          have h5 : ¬ j+(j+1) ≤ t := by omega
          by_cases hb0 : t ≤ 2*j+(-2)
          ·
            simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
            have hres : t%2 = 0 := by omega
            rw [hres]
            have htval : t = 2*j+(-2) := by omega
            rw [htval]
            have hjval : j = 2 := by omega
            rw [hjval]
            clear hj ht h0 h1 h2 h3 h4 h5
            grind only
          ·
            simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
            have hres : t%2 = 1 := by omega
            rw [hres]
            have htval : t = 2*j+(-1) := by omega
            rw [htval]
            have hjval : j = 1 := by omega
            rw [hjval]
            clear hj ht h0 h1 h2 h3 h4 h5
            grind only
        ·
          have h4 : ¬ (j+1) ≤ t := by omega
          have h5 : ¬ j+(j+1) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2 = 0 := by omega
          rw [hres]
          have htval : t = 2*j+(-2) := by omega
          rw [htval]
          have hjval : j = 1 := by omega
          rw [hjval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
  ·
    have h1 : ¬ t ≤ 2*j-2-0-1 := by omega
    by_cases h2 : j+1 ≤ t
    ·
      have h3 : j ≤ t := by omega
      have h4 : (j+1) ≤ t := by omega
      by_cases h5 : j+(j+1) ≤ t
      ·
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
      ·
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        have htval : t = 2*j+(0) := by omega
        rw [htval]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
    ·
      have h3 : j ≤ t := by omega
      have h4 : ¬ (j+1) ≤ t := by omega
      have h5 : ¬ j+(j+1) ≤ t := by omega
      simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
      have htval : t = 2*j+(0) := by omega
      rw [htval]
      have hjval : j = 0 := by omega
      rw [hjval]
      clear hj ht h0 h1 h2 h3 h4 h5
      grind only
private theorem update10 (j t : Int) (hj : 0 ≤ j) (ht : 0 ≤ t) :
    clipped true false (j+1) t - clipped true false j t = 24*increment (j+0) j (2*t+0) := by
  have hn := norm_increment false j (j+0) t ht
  rw [norm_clipped true false (j+1) t ht, norm_clipped true false j t ht]
  simp only [bit, Bool.false_eq_true, ite_true, ite_false] at hn ⊢
  rw [hn]
  clear hn
  by_cases h0 : t ≤ 2*(j+1)-2-1-0
  ·
    by_cases h1 : t ≤ 2*j-2-1-0
    ·
      by_cases h2 : j+1 ≤ t
      ·
        have h3 : j ≤ t := by omega
        have h4 : (j+0) ≤ t := by omega
        have h5 : ¬ j+(j+0) ≤ t := by omega
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
      ·
        by_cases h3 : j ≤ t
        ·
          have h4 : (j+0) ≤ t := by omega
          have h5 : ¬ j+(j+0) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have htval : t = 1*j+(0) := by omega
          rw [htval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
        ·
          have h4 : ¬ (j+0) ≤ t := by omega
          have h5 : ¬ j+(j+0) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
    ·
      by_cases h2 : j+1 ≤ t
      ·
        have h3 : j ≤ t := by omega
        have h4 : (j+0) ≤ t := by omega
        have h5 : ¬ j+(j+0) ≤ t := by omega
        by_cases hb0 : t ≤ 2*j+(-2)
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2=0 ∨ t%2=1 := by omega
          have htval : t = 2*j+(-2) := by omega
          rw [htval] at hres ⊢
          rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2=0 ∨ t%2=1 := by omega
          have htval : t = 2*j+(-1) := by omega
          rw [htval] at hres ⊢
          rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
      ·
        by_cases h3 : j ≤ t
        ·
          have h4 : (j+0) ≤ t := by omega
          have h5 : ¬ j+(j+0) ≤ t := by omega
          by_cases hb0 : t ≤ 2*j+(-2)
          ·
            simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
            have hres : t%2=0 ∨ t%2=1 := by omega
            have htval : t = 2*j+(-2) := by omega
            rw [htval] at hres ⊢
            have hjval : j = 2 := by omega
            rw [hjval] at hres ⊢
            rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
          ·
            simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
            have hres : t%2=0 ∨ t%2=1 := by omega
            have htval : t = 2*j+(-1) := by omega
            rw [htval] at hres ⊢
            have hjval : j = 1 := by omega
            rw [hjval] at hres ⊢
            rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
        ·
          have h4 : ¬ (j+0) ≤ t := by omega
          have h5 : ¬ j+(j+0) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2=0 ∨ t%2=1 := by omega
          have htval : t = 2*j+(-2) := by omega
          rw [htval] at hres ⊢
          have hjval : j = 1 := by omega
          rw [hjval] at hres ⊢
          rcases hres with hres|hres <;> rw [hres] <;> (clear hj ht h0 h1 h2 h3 h4 h5; grind only)
  ·
    have h1 : ¬ t ≤ 2*j-2-1-0 := by omega
    by_cases h2 : j+1 ≤ t
    ·
      have h3 : j ≤ t := by omega
      have h4 : (j+0) ≤ t := by omega
      have h5 : j+(j+0) ≤ t := by omega
      simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
      clear hj ht h0 h1 h2 h3 h4 h5
      grind only
    ·
      have h3 : j ≤ t := by omega
      have h4 : (j+0) ≤ t := by omega
      have h5 : j+(j+0) ≤ t := by omega
      simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
      clear hj ht h0 h1 h2 h3 h4 h5
      grind only
private theorem update11 (j t : Int) (hj : 0 ≤ j) (ht : 0 ≤ t) :
    clipped true true (j+1) t - clipped true true j t = 24*increment (j+0) j (2*t+1) := by
  have hn := norm_increment true j (j+0) t ht
  rw [norm_clipped true true (j+1) t ht, norm_clipped true true j t ht]
  simp only [bit, Bool.false_eq_true, ite_true, ite_false] at hn ⊢
  rw [hn]
  clear hn
  by_cases h0 : t ≤ 2*(j+1)-2-1-1
  ·
    by_cases h1 : t ≤ 2*j-2-1-1
    ·
      by_cases h2 : j+1 ≤ t
      ·
        have h3 : j ≤ t := by omega
        have h4 : (j+0) ≤ t := by omega
        have h5 : ¬ j+(j+0) ≤ t := by omega
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
      ·
        by_cases h3 : j ≤ t
        ·
          have h4 : (j+0) ≤ t := by omega
          have h5 : ¬ j+(j+0) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have htval : t = 1*j+(0) := by omega
          rw [htval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
        ·
          have h4 : ¬ (j+0) ≤ t := by omega
          have h5 : ¬ j+(j+0) ≤ t := by omega
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
    ·
      by_cases h2 : j+1 ≤ t
      ·
        have h3 : j ≤ t := by omega
        have h4 : (j+0) ≤ t := by omega
        have h5 : ¬ j+(j+0) ≤ t := by omega
        by_cases hb0 : t ≤ 2*j+(-3)
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2 = 1 := by omega
          rw [hres]
          have htval : t = 2*j+(-3) := by omega
          rw [htval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
        ·
          simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
          have hres : t%2 = 0 := by omega
          rw [hres]
          have htval : t = 2*j+(-2) := by omega
          rw [htval]
          clear hj ht h0 h1 h2 h3 h4 h5
          grind only
      ·
        by_cases h3 : j ≤ t
        ·
          have h4 : (j+0) ≤ t := by omega
          have h5 : ¬ j+(j+0) ≤ t := by omega
          by_cases hb0 : t ≤ 2*j+(-3)
          ·
            simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
            have hres : t%2 = 1 := by omega
            rw [hres]
            have htval : t = 2*j+(-3) := by omega
            rw [htval]
            have hjval : j = 3 := by omega
            rw [hjval]
            clear hj ht h0 h1 h2 h3 h4 h5
            grind only
          ·
            simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
            have hres : t%2 = 0 := by omega
            rw [hres]
            have htval : t = 2*j+(-2) := by omega
            rw [htval]
            have hjval : j = 2 := by omega
            rw [hjval]
            clear hj ht h0 h1 h2 h3 h4 h5
            grind only
        ·
          have h4 : ¬ (j+0) ≤ t := by omega
          have h5 : ¬ j+(j+0) ≤ t := by omega
          by_cases hb0 : t ≤ 2*j+(-3)
          ·
            simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
            have hres : t%2 = 1 := by omega
            rw [hres]
            have htval : t = 2*j+(-3) := by omega
            rw [htval]
            have hjval : j = 2 := by omega
            rw [hjval]
            clear hj ht h0 h1 h2 h3 h4 h5
            grind only
          ·
            simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
            have hres : t%2 = 0 := by omega
            rw [hres]
            have htval : t = 2*j+(-2) := by omega
            rw [htval]
            have hjval : j = 1 := by omega
            rw [hjval]
            clear hj ht h0 h1 h2 h3 h4 h5
            grind only
  ·
    have h1 : ¬ t ≤ 2*j-2-1-1 := by omega
    by_cases h2 : j+1 ≤ t
    ·
      have h3 : j ≤ t := by omega
      have h4 : (j+0) ≤ t := by omega
      by_cases h5 : j+(j+0) ≤ t
      ·
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
      ·
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        have htval : t = 2*j+(-1) := by omega
        rw [htval]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
    ·
      have h3 : j ≤ t := by omega
      have h4 : (j+0) ≤ t := by omega
      by_cases h5 : j+(j+0) ≤ t
      ·
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
      ·
        simp only [h0, h1, h2, h3, h4, h5, decide_true, decide_false, ite_true, ite_false, value, b3, b4, l4, Bool.false_eq_true]
        have htval : t = 2*j+(-1) := by omega
        rw [htval]
        have hjval : j = 1 := by omega
        rw [hjval]
        clear hj ht h0 h1 h2 h3 h4 h5
        grind only
theorem scaled_pair_eq (e p : Bool) (m : Nat) (t : Int) (ht : 0 ≤ t) :
    clipped e p m t = 24 * pairCoeff e m (2*t+(if p then 1 else 0)) := by
  induction m with
  | zero =>
    have hb : ¬(0 ≤ 2*t+(if p then 1 else 0) ∧ 2*t+(if p then 1 else 0) ≤ 4*(0:Int)-4-(if e then 2 else 0)) := by
      cases p <;> cases e <;> simp <;> omega
    unfold clipped
    simp only [Int.natCast_zero]
    rw [ite_eq_right hb]
    rfl
  | succ j ih =>
    rw [pairCoeff, batch_eq _ _ _ (by omega)]
    cases e <;> cases p
    · have hu := update00 (j:Int) t (by omega) ht
      simp only [Bool.false_eq_true,ite_false,Int.natCast_succ,Int.add_zero] at hu ih ⊢
      omega
    · have hu := update01 (j:Int) t (by omega) ht
      simp only [Bool.false_eq_true,ite_false,ite_true,Int.natCast_succ,Int.add_zero] at hu ih ⊢
      omega
    · have hu := update10 (j:Int) t (by omega) ht
      simp only [Bool.false_eq_true,ite_false,ite_true,Int.natCast_succ,Int.add_zero] at hu ih ⊢
      omega
    · have hu := update11 (j:Int) t (by omega) ht
      simp only [ite_true,Int.natCast_succ,Int.add_zero] at hu ih ⊢
      omega

private theorem batch_nonneg (n : Nat) (j d : Int) : 0 ≤ batch n j d := by
  induction n with
  | zero => simp [batch]
  | succ n ih => unfold batch; unfold rect; omega

private theorem pairs_nonneg (e : Bool) (m : Nat) (d : Int) : 0 ≤ pairCoeff e m d := by
  induction m with
  | zero => simp [pairCoeff]
  | succ j ih =>
    have hb := batch_nonneg (if e then j else j+1) j d
    rw [pairCoeff]; omega

/-- Every degree in the support has a positive coefficient. -/
theorem pair_positive (e : Bool) (m : Nat) (d : Int) (hd : 0 ≤ d)
    (hs : d ≤ 4*(m:Int)-4-(if e then 2 else 0)) : 0 < pairCoeff e m d := by
  cases m with
  | zero => cases e <;> simp at hs <;> omega
  | succ j =>
    have prev := pairs_nonneg e j d
    rw [pairCoeff]
    cases e
    · simp only [Bool.false_eq_true,ite_false,Int.natCast_succ] at hs ⊢
      rw [batch]
      have hb := batch_nonneg j j d
      unfold rect
      omega
    · simp only [ite_true,Int.natCast_succ] at hs ⊢
      cases j with
      | zero => simp at hs; omega
      | succ i =>
        rw [batch]
        have hb := batch_nonneg i (i+1:Nat) d
        unfold rect
        simp only [Int.natCast_succ] at hs hb prev ⊢
        omega

/-- Strict stride-two log-concavity for the actual coefficients of both
degree-two symmetric functions in odd q-integers, on their full supports. -/
theorem pair_strict (e p : Bool) (m : Nat) (t : Int) (ht : 0 ≤ t)
    (hs : t ≤ 2*(m:Int)-(4+(if p then 1 else 0)+(if e then 1 else 0))) :
    let d := 2*t+(if p then 1 else 0)
    pairCoeff e m d * pairCoeff e m (d+4) < (pairCoeff e m (d+2))^2 := by
  dsimp only
  have h := strict_parity_gap e p m t ht hs
  have id (s : Int) (hl : t ≤ s) (hu : s ≤ t+2) :
      coeff24 e p m s = 24*pairCoeff e m (2*s+(if p then 1 else 0)) := by
    have cond : 0 ≤ 2*s+(if p then 1 else 0) ∧ 2*s+(if p then 1 else 0) ≤ 4*(m:Int)-4-(if e then 2 else 0) := by
      cases e <;> cases p <;> simp_all <;> omega
    simpa [clipped,cond] using scaled_pair_eq e p m s (by omega)
  rw [id t (by omega) (by omega),id (t+2) (by omega) (by omega),id (t+1) (by omega) (by omega)] at h
  have d4 : 2*(t+2)+(if p then 1 else 0) = (2*t+(if p then 1 else 0))+4 := by omega
  have d2 : 2*(t+1)+(if p then 1 else 0) = (2*t+(if p then 1 else 0))+2 := by omega
  rw [d4,d2] at h
  grind only
#print axioms pair_strict
#print axioms pair_positive

/-- Coefficient of q^v in [2*j+1]_q, with zero extension. -/
def oddInteger (j : Nat) (v : Int) : Int := if 0 ≤ v ∧ v ≤ 2*(j:Int) then 1 else 0

/-- Partial convolution with the odd-width q-integer. The exponents assigned
to the first factor are 0,...,a−1. -/
private def splitSum : Nat → Nat → Int → Int
  | 0, _, _ => 0
  | a+1, j, d => splitSum a j d + oddInteger j (d-(a:Int))

/-- Literal coefficient of the product [2*i+1]_q [2*j+1]_q. -/
def productCoeff (i j : Nat) (d : Int) : Int := splitSum (2*i+1) j d

private theorem split_eq (a j : Nat) (d : Int) :
    splitSum a j d = max 0 (min (a:Int) (d+1) - max 0 (d-2*(j:Int))) := by
  induction a with
  | zero => simp only [splitSum,Int.natCast_zero]; omega
  | succ a ih =>
    rw [splitSum,ih]
    unfold oddInteger
    split <;> simp only [Int.natCast_succ] <;> omega

theorem product_eq_rect (i j : Nat) (d : Int) :
    productCoeff i j d = rect d i j := by
  unfold productCoeff rect
  rw [split_eq]
  omega

private def productSum : Nat → Nat → Int → Int
  | 0, _, _ => 0
  | m+1, j, d => productSum m j d + productCoeff m j d

private theorem productSum_eq (m j : Nat) (d : Int) :
    productSum m j d = batch m j d := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [productSum,batch,ih,product_eq_rect]

/-- Coefficients of e₂ (strict pairs) or h₂ (weak pairs) of the m explicit
q-integers. Each summand is a convolution of two factors. -/
def symmetricTwo (e : Bool) : Nat → Int → Int
  | 0, _ => 0
  | j+1, d => symmetricTwo e j d + productSum (if e then j else j+1) j d

theorem symmetricTwo_eq (e : Bool) (m : Nat) (d : Int) :
    symmetricTwo e m d = pairCoeff e m d := by
  induction m with
  | zero => rfl
  | succ j ih => simp only [symmetricTwo,pairCoeff,ih,productSum_eq]

/-- Sagan--Swanson Theorem 2.1(a,b), specialized to k=n−2.
The signless first kind uses n variables, the second kind uses n−1. -/
def originalSecond (first : Bool) (n : Nat) (d : Int) : Int :=
  symmetricTwo first (if first then n else n-1) d

/-- Strict log-concavity on both parity subsequences for every original row
n≥2 and starting degree d such that d,d+2,d+4 all lie in the support. -/
theorem original_second_strict (first : Bool) (n : Nat) (d : Int)
    (hn : 2 ≤ n) (hd : 0 ≤ d)
    (hs : d+4 ≤ 4*(n:Int)-(if first then 6 else 8)) :
    originalSecond first n d * originalSecond first n (d+4) <
      originalSecond first n (d+2)^2 := by
  let odd := decide (d%2=1)
  let m := if first then n else n-1
  have de : 2*(d/2)+(if odd then 1 else 0)=d := by
    by_cases hr : d%2=1
    · simp [odd,hr]; omega
    · simp [odd,hr]; omega
  have dm : ((n-1:Nat):Int)=(n:Int)-1 := by omega
  have bound : d/2 ≤ 2*(m:Int)-(4+(if odd then 1 else 0)+(if first then 1 else 0)) := by
    by_cases hr : d%2=1 <;> cases first <;>
      simp [m,odd,hr,dm] at hs de ⊢ <;> omega
  have h := pair_strict first odd m (d/2) (by omega) bound
  dsimp only at h
  rw [de] at h
  unfold originalSecond
  simpa only [symmetricTwo_eq] using h

theorem original_second_positive (first : Bool) (n : Nat) (d : Int)
    (hn : 2 ≤ n) (hd : 0 ≤ d)
    (hs : d ≤ 4*(n:Int)-(if first then 6 else 8)) :
    0 < originalSecond first n d := by
  unfold originalSecond
  rw [symmetricTwo_eq]
  apply pair_positive _ _ _ hd
  cases first <;> simp at * <;> omega

#print axioms original_second_strict
#print axioms original_second_positive

end SecondDiagonal

namespace SecondDiagonal

/-- Adding the largest allowed index contributes the sum of its pair products. -/
theorem symmetricTwo_step (e : Bool) (j : Nat) (d : Int) :
    symmetricTwo e (j+1) d = symmetricTwo e j d +
      ((List.range (if e then j else j+1)).map (fun i => productCoeff i j d)).sum := by
  have sum_eq (m : Nat) : productSum m j d =
      ((List.range m).map (fun i => productCoeff i j d)).sum := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.range_succ, productSum, ih]
  exact congrArg (symmetricTwo e j d + ·) (sum_eq _)

end SecondDiagonal
