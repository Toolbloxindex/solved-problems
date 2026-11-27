import RecurrenceBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Coefficientwise differentiation of elementary and complete symmetric
functions in odd q-integers. Marking a box removes its digit and retains
its location, counting multiplicity in the complete case. -/
namespace StirlingBoxes
open Finset
abbrev Seq := Int → Int

def box (i : Nat) (f : Seq) (d : Int) : Int :=
  ∑ j ∈ range (2*i+1), f (d-(j:Int))

def unit (d : Int) : Int := if d=0 then 1 else 0

def prev (e : Bool) (m : Nat) := if e then m else m+1

/-- Rank r on the first m odd q-integers. -/
def F (e : Bool) : Nat → Nat → Seq
  | 0, _ => unit
  | _+1, 0 => 0
  | r+1, m+1 => fun d => F e (r+1) m d + box m (F e r (prev e m)) d
termination_by r m => (r,m)

/-- The partial derivative in the i-th alphabet letter, before substitution. -/
def mark (e : Bool) (i : Nat) : Nat → Nat → Seq
  | 0, _ => 0
  | _+1, 0 => 0
  | r+1, m+1 => fun d => mark e i (r+1) m d + box m (mark e i r (prev e m)) d +
      (if i=m then F e r (prev e m) d else 0)
termination_by r m => (r,m)

theorem F_succ (e : Bool) (r m : Nat) (d : Int) :
    F e (r+1) (m+1) d = F e (r+1) m d + box m (F e r (prev e m)) d := by rw [F]

theorem mark_succ (e : Bool) (i r m : Nat) (d : Int) :
    mark e i (r+1) (m+1) d = mark e i (r+1) m d + box m (mark e i r (prev e m)) d +
        (if i=m then F e r (prev e m) d else 0) := by rw [mark]

theorem box_eq_qmul (i : Nat) (f : Seq) (d : Int) :
    box i f d = FirstColumn.qmul f d (2*i+1) := by
  suffices ∀ w : Nat, (∑ j ∈ range w, f (d-(j:Int))) = FirstColumn.qmul f d w from this _
  intro w
  induction w with
  | zero => simp [FirstColumn.qmul]
  | succ w ih => rw [sum_range_succ, ih]; rfl

theorem box_mono {f g : Seq} (h : ∀ d, f d ≤ g d) (i : Nat) (d : Int) :
    box i f d ≤ box i g d := sum_le_sum fun _ _ => h _

theorem box_nn {f : Seq} (h : ∀ d, 0 ≤ f d) (i : Nat) (d : Int) :
    0 ≤ box i f d := sum_nonneg fun _ _ => h _

theorem box_ge {f : Seq} (h : ∀ d, 0 ≤ f d) (i : Nat) (d : Int) :
    f d ≤ box i f d := by
  simpa [box] using (single_le_sum (f := fun j : Nat => f (d-(j:Int)))
    (fun j _ => h _) (show 0 ∈ range (2*i+1) by simp))

theorem box_add (i : Nat) (f g : Seq) (d : Int) :
    box i (fun z => f z + g z) d = box i f d + box i g d := by simp [box, sum_add_distrib]

theorem box_comm (i j : Nat) (f : Seq) (d : Int) :
    box i (box j f) d = box j (box i f) d := by
  unfold box
  rw [sum_comm]
  congr 1
  ext a
  congr 1
  ext b
  congr 1
  omega

theorem F_nn (e : Bool) (r m : Nat) (d : Int) : 0 ≤ F e r m d := by
  induction r generalizing m d with
  | zero => simp [F,unit]; split <;> decide
  | succ r ih =>
    induction m with
    | zero => simp [F]
    | succ m hm => rw [F]; exact add_nonneg hm (box_nn (ih _) _ _)

theorem mark_nn (e : Bool) (i r m : Nat) (d : Int) : 0 ≤ mark e i r m d := by
  induction r generalizing m d with
  | zero => simp [mark]
  | succ r ih =>
    induction m with
    | zero => simp [mark]
    | succ m hm =>
      rw [mark]
      exact add_nonneg (add_nonneg hm (box_nn (ih _) _ _)) (by split <;> simp [F_nn])

theorem mark_off (e : Bool) (i r m : Nat) (h : m ≤ i) : mark e i r m = 0 := by
  induction r generalizing m with
  | zero => simp [mark]
  | succ r ih =>
    induction m with
    | zero => simp [mark]
    | succ m hm =>
      funext d
      rw [mark, hm (by omega), ih (prev e m) (by unfold prev; split <;> omega)]
      simp [box,show i≠m by omega]

theorem first_mark_le (i r m : Nat) (d : Int) : mark true i r m d ≤ F true r m d := by
  induction r generalizing m d with
  | zero => simpa [mark] using F_nn true 0 m d
  | succ r ih =>
    induction m with
    | zero => simp [mark,F]
    | succ m hm =>
      rw [mark,F]
      by_cases eq : i=m
      · subst i
        simp only [prev, ite_true, mark_off true m (r+1) m (le_refl _),
          mark_off true m r m (le_refl _), Pi.zero_apply, box, sum_const_zero, zero_add]
        have := box_ge (F_nn true r m) m d
        have := F_nn true (r+1) m d
        unfold box at *
        omega
      · simp only [eq, ite_false, add_zero]
        exact add_le_add hm (box_mono (ih _) _ _)

theorem second_mark_step (i r m : Nat) (hi : i<m) (d : Int) :
    mark false i (r+1) m d = F false r m d + box i (mark false i r m) d := by
  induction r generalizing m d with
  | zero =>
    induction m with
    | zero => omega
    | succ m hm =>
      by_cases h : i=m
      · subst i; simp [mark, mark_off false m 1 m (le_refl _), F, box, prev]
      · rw [mark_succ, hm (by omega)]
        simp [F,mark,box,h]
  | succ r ih =>
    induction m with
    | zero => omega
    | succ m hm =>
      by_cases h : i=m
      · subst i
        rw [mark, mark_off false m (r+2) m (le_refl _)]
        simp [prev,add_comm]
      · rw [mark_succ, hm (by omega)]
        simp only [prev, Bool.false_eq_true, ite_false, h, add_zero]
        have hx : mark false i (r+1) (m+1) = fun z => F false r (m+1) z +
            box i (mark false i r (m+1)) z := funext (ih _ (by omega))
        -- Expand the inner marked successor and commute the two windows.
        conv_lhs => rw [hx, box_add, box_comm m i]
        have hy : mark false i (r+1) (m+1) = fun z =>
            mark false i (r+1) m z + box m (mark false i r (m+1)) z := by
          funext z; rw [mark]; simp [prev,h]
        rw [hy, box_add, F]
        simp [prev]
        ring

theorem second_mark_mono {i j : Nat} (h : i≤j) (r m : Nat) (hj : j<m) (d : Int) :
    mark false i r m d ≤ mark false j r m d := by
  induction r generalizing d with
  | zero => simp [mark]
  | succ r ih =>
    rw [second_mark_step i r m (by omega), second_mark_step j r m hj]
    exact add_le_add (le_refl _) (by
      apply le_trans (box_mono ih i d)
      apply sum_le_sum_of_subset_of_nonneg
      · apply range_mono; omega
      · intro a _ _; exact mark_nn _ _ _ _ _)

end StirlingBoxes

namespace StirlingBoxes
open Finset
theorem scale_sum (c : Int) (n : Nat) (f : Nat → Int) :
  c * (∑ i ∈ range n, f i) = ∑ i ∈ range n, c * f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, mul_add, ih]
end StirlingBoxes

namespace StirlingBoxes
open Finset

theorem pick (m l : Nat) (h : m<l) (f : Nat → Int) :
    (∑ j ∈ range l, if j=m then f j else 0) = f m := by
  rw [sum_eq_single m]
  · simp
  · intro j _ hj; simp [hj]
  · intro hj; exact (hj (mem_range.mpr h)).elim

def loss (r : Nat) (f : Seq) (d : Int) : Int :=
  ((r:Int)+d)*f d - (d+1)*f (d+1)

def weight (i : Nat) : Int := 2*(i:Int)+1

/-- The loss in a product with [w] is the cost of saturating that digit. -/
theorem loss_box (r i : Nat) (f : Seq) (d : Int) :
    loss (r+1) (box i f) d = box i (loss r f) d + weight i * f (d-2*(i:Int)) := by
  suffices h : ∀ w : Nat, loss (r+1) (fun z => FirstColumn.qmul f z w) d =
      FirstColumn.qmul (loss r f) d w + (w:Int)*f (d-(w:Int)+1) by
    simp only [funext (box_eq_qmul i f), box_eq_qmul, h, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, weight]
    rw [show d-(2*(i:Int)+1)+1=d-2*(i:Int) by ring]
  intro w
  induction w with
  | zero => simp [loss,FirstColumn.qmul]
  | succ w ih =>
    simp only [loss, FirstColumn.qmul, Nat.cast_succ] at ih ⊢
    rw [show d+1-(w:Int)=d-(w:Int)+1 by ring,
      show d-((w:Int)+1)+1=d-(w:Int) by ring]
    linarith only [ih]

theorem box_sum (i l : Nat) (g : Nat → Seq) (d : Int) :
    box i (fun z => ∑ j ∈ range l, g j z) d = ∑ j ∈ range l, box i (g j) d := by
  unfold box; rw [sum_comm]

theorem box_scale_shift (m : Nat) (f : Seq) (c s d : Int) :
    box m (fun z => c * f (z-s)) d = c * box m f (d-s) := by
  simp only [box, scale_sum]
  apply sum_congr rfl
  intro j _
  rw [show d-(j:Int)-s = d-s-(j:Int) by ring]

/-- Bound the total number of marks by the number of digit slots. The
ambient alphabet l may exceed m; those locations give zero. -/
theorem total_marks (e : Bool) (r m l : Nat) (hl : m≤l) (d : Int) :
    ∑ i ∈ range l, mark e i r m d ≤ (r:Int)*F e r m d := by
  induction r generalizing m d with
  | zero => simp [mark]
  | succ r ih =>
    induction m with
    | zero => simp [mark,F]
    | succ m hm =>
      have hp : prev e m ≤ l := by unfold prev; split <;> omega
      have h1 := hm (by omega)
      have h2 := box_mono (fun z => ih _ hp z) m d
      rw [box_sum] at h2
      have sc : box m (fun z => (r:Int)*F e r (prev e m) z) d =
          (r:Int)*box m (F e r (prev e m)) d := by simp [box,scale_sum]
      rw [sc] at h2
      simp only [mark_succ e _ r m, sum_add_distrib, pick m l (by omega), Nat.cast_succ, F_succ e r m]
      simp only [Nat.cast_succ] at h1
      have h3 := box_ge (F_nn e r (prev e m)) m d
      linarith only [h1,h2,h3]

/-- Exact coefficient identity from marking the saturated digit. -/
theorem loss_marks (e : Bool) (r m l : Nat) (hl : m ≤ l) (d : Int) :
    loss r (F e r m) d = ∑ i ∈ range l, weight i * mark e i r m (d-2*(i:Int)) := by
  induction r generalizing m d with
  | zero =>
    simp only [F,mark,Pi.zero_apply,mul_zero,sum_const_zero,loss,unit,Nat.cast_zero,zero_add]
    split <;> split <;> omega
  | succ r ih =>
    induction m with
    | zero => simp [F,mark,loss]
    | succ m hm =>
      have hp : prev e m ≤ l := by unfold prev; split <;> omega
      have h1 := hm (by omega)
      have h2 := loss_box r m (F e r (prev e m)) d
      rw [funext (ih _ hp), box_sum] at h2
      simp only [box_scale_shift] at h2
      have extra : (∑ i ∈ range l, weight i * (if i=m then F e r (prev e m) (d-2*(i:Int)) else 0))
          = weight m * F e r (prev e m) (d-2*(m:Int)) := by
        simp only [mul_ite,mul_zero,pick m l (by omega)]
      simp only [mark_succ e _ r m, mul_add, sum_add_distrib, extra]
      rw [← h1]
      rw [funext (F_succ e r m)]
      unfold loss at h2 ⊢
      linarith only [h2]

private theorem sum_tail_const (i m : Nat) (a : Int) (h : i<m) :
    (∑ j ∈ range m, if i≤j then a else 0) = ((m:Int)-(i:Int))*a := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [sum_range_succ]
    by_cases h' : i<m
    · rw [ih h']; simp only [show i≤m by omega, ite_true, Nat.cast_succ]; ring
    · have hm : m=i := by omega
      subst m
      rw [sum_eq_zero (fun j hj => ite_eq_right (by have := mem_range.mp hj; omega))]
      simp

theorem second_mass (i r m : Nat) (hi : i<m) (d : Int) :
    (m:Int)*mark false i r m d ≤ (r:Int)*((i:Int)+1)*F false r m d := by
  let f := fun j => mark false j r m d
  have h : (m-i:Int)*f i ≤ ∑ j ∈ range m, f j := by
    have hle : ∑ j ∈ range m, (if i≤j then f i else 0) ≤ ∑ j ∈ range m, f j := by
      apply sum_le_sum; intro j hj
      split
      · exact second_mark_mono ‹_› r m (mem_range.mp hj) d
      · exact mark_nn _ _ _ _ _
    have heq : ∑ j ∈ range m, (if i≤j then f i else 0) = ((m:Int)-(i:Int))*f i := by
      exact sum_tail_const i m (f i) hi
    rwa [heq] at hle
  have h2 := total_marks false r m m (le_refl _) d
  have h3 : m ≤ (i+1)*(m-i) := by
    have : 1 ≤ m-i := by omega
    nlinarith [Nat.sub_add_cancel (by omega : i≤m), Nat.mul_le_mul_left i this]
  have h4 : (m:Int) ≤ ((i:Int)+1)*((m:Int)-(i:Int)) := by
    have hh : ((m:Nat):Int) ≤ ((i:Int)+1)*((m-i:Nat):Int) := by exact_mod_cast h3
    simpa [Nat.cast_sub (by omega : i≤m)] using hh
  have h5 := mul_le_mul_of_nonneg_right h4 (mark_nn false i r m d)
  have h6 := mul_le_mul_of_nonneg_left (le_trans h h2) (show (0:Int)≤(i:Int)+1 by omega)
  dsimp [f] at h5 h6
  linarith only [h5,h6]

end StirlingBoxes

namespace StirlingBoxes
open Finset StirlingRecurrence

private theorem first_above (r m : Nat) (h : m<r) : F true r m = 0 := by
  induction m generalizing r with
  | zero => cases r with
    | zero => omega
    | succ r => simp [F]
  | succ m ih =>
    cases r with
    | zero => omega
    | succ r =>
      funext d
      rw [F_succ, ih (r+1) (by omega), show prev true m = m by rfl, ih r (by omega)]
      simp [box]

theorem box_zero_column (r : Nat) : F false r 1 = unit := by
  induction r with
  | zero => rw [F]
  | succ r ih =>
    funext d
    rw [F_succ, show prev false 0=1 by rfl, ih]
    simp [F,box]

/-- Formal identification with the source equations, at every rank. -/
theorem source (e : Bool) (n k r : Nat) (hr : n=k+r) :
    coeff e n k = F e r (if e then n else k+1) := by
  induction n generalizing k r with
  | zero =>
    have hk : k=0 := by omega
    have hr' : r=0 := by omega
    subst k; subst r
    funext d
    simp [recurrence_diagonal,F,unit]
  | succ n ih =>
    cases r with
    | zero =>
      have eq : k=n+1 := by omega
      subst k
      rw [recurrence_diagonal,F]; rfl
    | succ r =>
      cases k with
      | zero =>
        have eq : n=r := by omega
        subst r
        cases e <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · rw [box_zero_column]; funext d
          exact FirstColumn.column_zero _ _
        · funext d
          rw [F_succ, first_above (n+1) n (by omega)]
          change FirstColumn.qmul (coeff true n 0) d (2*n+1) = 0 + box n (F true n n) d
          rw [ih 0 n (by omega), box_eq_qmul]
          simp
      | succ k =>
        funext d
        have a := ih k (r+1) (by omega)
        have b := ih (k+1) r (by omega)
        cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true] at *
        · rw [F_succ]
          change coeff false n k d + FirstColumn.qmul (coeff false n (k+1)) d _ = _
          rw [a,b,box_eq_qmul]; rfl
        · rw [F_succ]
          change coeff true n k d + FirstColumn.qmul (coeff true n (k+1)) d _ = _
          rw [a,b,box_eq_qmul]; rfl

theorem F_off (e : Bool) (r m : Nat) (d : Int) (h : d<0) : F e r m d=0 := by
  induction r generalizing m d with
  | zero => simp [F,unit,show d≠0 by omega]
  | succ r ih =>
    induction m with
    | zero => simp [F]
    | succ m hm =>
      rw [F_succ,hm,zero_add]
      apply sum_eq_zero
      intro j _
      exact ih _ _ (by omega)

end StirlingBoxes
