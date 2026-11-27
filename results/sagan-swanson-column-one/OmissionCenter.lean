import MarkedAlphabet
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace StirlingBoxes.OmissionCenter
open Finset StirlingRecurrence

/-- Sum of the radii of the first n windows. -/
def center : ℕ → ℤ
  | 0 => 0
  | n+1 => center n+n

private structure Radial (c : ℤ) (f : Seq) : Prop where
  mirror : ∀ x, f (2*c-x)=f x
  rise : ∀ x, x<c → f x≤f (x+1)

private theorem left_pair {c : ℤ} {f : Seq} (h : Radial c f) (x y : ℤ)
    (xy : x≤y) (mid : x+y≤2*c) : f x≤f y := by
  have climb (u v : ℤ) (uv : u≤v) (vc : v≤c) : f u≤f v := by
    obtain ⟨n,eq⟩ := Int.le.dest uv
    have steps (n : ℕ) (hc : u+(n:ℤ)≤c) : f u≤f (u+n) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.cast_succ,←add_assoc]
        exact (ih (by omega)).trans (h.rise _ (by omega))
    exact eq ▸ steps n (by omega)
  by_cases le : y≤c
  · exact climb x y xy le
  · rw [←h.mirror y]
    exact climb _ _ (by omega) (by omega)

theorem slide (i : ℕ) (f : Seq) (x : ℤ) :
    box i f (x+1)-box i f x=f (x+1)-f (x-2*i) := by
  unfold box
  rw [sum_range_succ',sum_range_succ]
  simp only [Nat.cast_zero,sub_zero,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_succ]
  simp_rw [show ∀ j : ℕ,x+1-((j:ℤ)+1)=x-j by intro j;omega]
  ring

private theorem radial_box {c : ℤ} {f : Seq} (h : Radial c f) (i : ℕ) :
    Radial (c+i) (box i f) := by
  constructor
  · intro x
    unfold box
    rw [←sum_range_reflect]
    apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    rw [show 2*(c+(i:ℤ))-x-((2*i+1-1-j:ℕ):ℤ)=2*c-(x-j) by omega,h.mirror]
  · intro x lt
    have H := left_pair h (x-2*i) (x+1) (by omega) (by omega)
    have := slide i f x
    omega

private inductive Band (a b : ℤ) : Seq → Prop
  | one {c f} : a≤c → c≤b → Radial c f → Band a b f
  | add {f g} : Band a b f → Band a b g → Band a b (fun z => f z+g z)

private theorem band_box {a b A B : ℤ} {f : Seq} (h : Band a b f) (i : ℕ)
    (lo : A≤a+i) (hi : b+i≤B) : Band A B (box i f) := by
  induction h with
  | one l u rad => exact .one (by omega) (by omega) (radial_box rad i)
  | add _ _ ih jh =>
    have eq : ∀ f g : Seq, box i (fun z => f z+g z)=fun z => box i f z+box i g z :=
      fun f g => funext (box_add i f g)
    rw [eq]
    exact .add ih jh

private theorem wings {a b : ℤ} {f : Seq} (h : Band a b f) (x : ℤ) :
    (x<a → f x≤f (x+1)) ∧ (b≤x → f (x+1)≤f x) := by
  induction h with
  | @one c f l u rad =>
    constructor
    · intro hx;exact rad.rise x (by omega)
    · intro hx
      rw [←rad.mirror (x+1),←rad.mirror x]
      apply left_pair rad <;> omega
  | add _ _ ih jh =>
    exact ⟨fun hx => add_le_add (ih.1 hx) (jh.1 hx), fun hx => add_le_add (ih.2 hx) (jh.2 hx)⟩

private theorem concave_box {a b : ℤ} {f : Seq} (h : Band a b f) (i : ℕ) (d : ℤ)
    (lo : b≤d) (hi : d≤a+2*i) :
    box i f (d-1)+box i f (d+1)≤2*box i f d := by
  have A := (wings h d).2 lo
  have B := (wings h (d-1-2*i)).1 (by omega)
  have C := slide i f (d-1)
  have D := slide i f d
  rw [show d-1-2*(i:ℤ)+1=d-2*i by omega] at B
  rw [show d-1+1=d by omega] at C
  omega

private theorem zero_step (n : ℕ) : cb (n+1) 0=box n (cb n 0) :=
  funext fun d => (box_eq_qmul n (cb n 0) d).symm
private theorem one_step (n : ℕ) : cb (n+1) 1=fun d => cb n 0 d+box n (cb n 1) d := by
  funext d; rw [cb,box_eq_qmul]

private theorem full_radial (n : ℕ) : Radial (center n) (cb n 0) := by
  induction n with
  | zero =>
    constructor
    · intro x;simp [center,cb]
    · intro x hx;simp [center] at hx;simp [cb,show x≠0 by omega];split <;> decide
  | succ n ih => rw [zero_step];exact radial_box ih n

private theorem column_band (r : ℕ) : Band (center r) (center (r+1)) (cb (r+1) 1) := by
  induction r with
  | zero =>
    have eq : cb 1 1=cb 0 0 := by funext d;simp [cb,FirstColumn.qmul]
    rw [eq]
    exact .one le_rfl (by simp [center]) (full_radial 0)
  | succ r ih =>
    rw [one_step]
    apply Band.add
    · exact .one le_rfl (by simp only [center,Nat.cast_succ];omega) (full_radial _)
    · apply band_box ih
      · simp [center]
      · rfl

/-- Two ordered points whose midpoint is at or below the smallest omission
center have increasing column-one coefficients. -/
theorem column_one_left_pair (r : ℕ) (x y : ℤ) (hxy : x≤y)
    (hmid : x+y≤2*center r) : cb (r+1) 1 x≤cb (r+1) 1 y := by
  have H {a b : ℤ} {f : Seq} (h : Band a b f) (hm : x+y≤2*a) : f x≤f y := by
    induction h with
    | one lo hi rad => exact left_pair rad x y hxy (by omega)
    | add _ _ ih jh => exact add_le_add ih jh
  exact H (column_band r) hmid

/-- At every positive rank the whole first-kind column-one source is
arithmetically concave at each integer from T_r through T_(r+1)-1. -/
theorem column_one_concave (r : ℕ) (d : ℤ) (lo : center r≤d) (hi : d<center (r+1)) :
    let f := cb (r+1) 1
    f (d-1)+f (d+1)≤2*f d := by
  cases r with
  | zero => simp [center] at lo hi;omega
  | succ r =>
    dsimp only
    rw [one_step (r+1),zero_step r]
    have P := concave_box (Band.one (le_refl _) (le_refl _) (full_radial r)) r d
    have Q := concave_box (column_band r) (r+1) d
    simp only [center,Nat.cast_succ] at lo hi
    have H := P (by omega) (by omega)
    have J := Q (by simpa [center] using lo) (by omega)
    dsimp only
    omega

/-- The complete first-kind column one is ordinarily unimodal, including
every rank and both zero-padded tails. The peak lies between the smallest
and largest possible centers of the omitted-window products. -/
theorem column_one_unimodal (r : ℕ) :
    ∃ p : ℤ, center r≤p ∧ p≤center (r+1) ∧
      (∀ x : ℤ, x<p → cb (r+1) 1 x≤cb (r+1) 1 (x+1)) ∧
      (∀ x : ℤ, p≤x → cb (r+1) 1 (x+1)≤cb (r+1) 1 x) := by
  let a := center r
  let b := center (r+1)
  let f := cb (r+1) 1
  have width : b=a+r := rfl
  let P := fun j : ℕ => b≤a+j ∨ f (a+j+1)≤f (a+j)
  have endp : P r := Or.inl width.le
  have ex : ∃ j, P j := ⟨r,endp⟩
  let n := Nat.find ex
  let p := a+(n:ℤ)
  have nr : n≤r := Nat.find_min' ex endp
  have np : P n := Nat.find_spec ex
  have ap : a≤p := by dsimp [p];omega
  have pb : p≤b := by dsimp [p];omega
  change ∃ p : ℤ, a≤p ∧ p≤b ∧ (∀ x, x<p → f x≤f (x+1)) ∧ (∀ x, p≤x → f (x+1)≤f x)
  refine ⟨p,ap,pb,?_,?_⟩
  · intro x xp
    by_cases low : x<a
    · exact (wings (column_band r) x).1 low
    obtain ⟨j,eq⟩ := Int.le.dest (le_of_not_gt low)
    have jn : j<n := by dsimp [p] at xp;omega
    have h := Nat.find_min ex jn
    change ¬(b≤a+j ∨ f (a+j+1)≤f (a+j)) at h
    rw [eq] at h
    omega
  · intro x px
    by_cases high : b≤x
    · exact (wings (column_band r) x).2 high
    have step (j : ℕ) (room : p+j<b) : f (p+j+1)≤f (p+j) := by
      induction j with
      | zero =>
        simp only [Nat.cast_zero,add_zero] at room ⊢
        exact np.resolve_left (by change ¬b≤p;omega)
      | succ j ih =>
        rw [Nat.cast_succ,←add_assoc]
        have prev := ih (by omega)
        have cv := column_one_concave r (p+j+1) (by change a≤_;omega) (by omega)
        change f (p+j+1-1)+f (p+j+1+1)≤2*f (p+j+1) at cv
        rw [show p+(j:ℤ)+1-1=p+j by omega] at cv
        omega
    obtain ⟨j,eq⟩ := Int.le.dest px
    exact eq ▸ step j (by omega)

/-- The two parity subsequences are log-concave on the common central strip. -/
theorem column_one_central_parity (r : ℕ) (d : ℤ) (lo : center r<d) (hi : d+1<center (r+1)) :
    let f := cb (r+1) 1
    f (d-2)*f (d+2)≤f d^2 := by
  let f := cb (r+1) 1
  have cv (x : ℤ) (l : center r≤x) (u : x<center (r+1)) :
      f (x-1)+f (x+1)≤2*f x := column_one_concave r x l u
  have A := cv (d-1) (by omega) (by omega)
  have B := cv d (by omega) (by omega)
  have C := cv (d+1) (by omega) hi
  rw [show d-1-1=d-2 by omega,show d-1+1=d by omega] at A
  rw [show d+1-1=d by omega,show d+1+1=d+2 by omega] at C
  have nn (x : ℤ) : 0≤f x := by
    change 0≤coeff true (r+1) 1 x
    rw [source true _ _ r (by omega)]
    exact F_nn ..
  have H : f (d-2)+f (d+2)≤2*f d := by omega
  have sq := mul_self_le_mul_self (add_nonneg (nn _) (nn _)) H
  change f (d-2)*f (d+2)≤f d^2
  nlinarith only [sq,sq_nonneg (f (d-2)-f (d+2))]

/-- Product of the first n windows with the window at label i skipped. -/
def omitted : ℕ → ℕ → Seq
  | 0, _ => unit
  | n+1, i => if n=i then omitted n i else box n (omitted n i)

private theorem omitted_full (n i : ℕ) (h : n≤i) : omitted n i=cb n 0 := by
  induction n with
  | zero => funext d;simp [omitted,unit,cb]
  | succ n ih => rw [omitted,ite_eq_right (by omega),ih (by omega),zero_step]

theorem column_one_omissions (n : ℕ) (d : ℤ) :
    (∑ i ∈ range n, omitted n i d)=cb n 1 d := by
  induction n generalizing d with
  | zero => simp [cb]
  | succ n ih =>
    rw [sum_range_succ,one_step n]
    have eq (i : ℕ) (hi : i∈range n) : omitted (n+1) i d=box n (omitted n i) d := by
      rw [omitted,ite_eq_right (ne_of_gt (mem_range.mp hi))]
    rw [sum_congr rfl eq]
    simp only [omitted,omitted_full n n le_rfl,box]
    rw [sum_comm]
    simp [ih,add_comm]

/-- A single rational tilt a/b can use the actual weights of all omissions.
Its nonnegative total arithmetic curvature certifies the source determinant. -/
theorem parity_of_omission_payment (n : ℕ) (d a b : ℤ) (ha : 0<a)
    (left : 0≤cb n 1 (d-2))
    (paid : 0≤∑ i ∈ range n, (2*a*b*omitted n i d-b^2*omitted n i (d-2)-a^2*omitted n i (d+2))) :
    cb n 1 (d-2)*cb n 1 (d+2)≤cb n 1 d^2 := by
  simp only [sum_sub_distrib,←mul_sum,column_one_omissions] at paid
  have H := mul_nonneg left paid
  have S := sq_nonneg (a*cb n 1 d-b*cb n 1 (d-2))
  have Q : 0≤a^2*(cb n 1 d^2-cb n 1 (d-2)*cb n 1 (d+2)) := by
    nlinarith only [H,S]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right Q (sq_pos_of_pos ha))

/-- If the first coordinates balance, it suffices to check every two-term
positive combination that lies on the vertical axis. -/
theorem balanced_sum (s : Finset ℕ) (A B : ℕ → ℤ)
    (total : ∑ i ∈ s, A i = 0)
    (vertical : ∀ i ∈ s, A i = 0 → B i ≤ 0)
    (cross : ∀ i ∈ s, ∀ j ∈ s, 0 < A i → A j < 0 →
      (-A j)*B i + A i*B j ≤ 0) : ∑ i ∈ s, B i ≤ 0 := by
  classical
  let p := s.filter fun i => 0 < A i
  by_cases ne : p.Nonempty
  · obtain ⟨k,hk,best⟩ := p.exists_max_image (fun i => (B i : ℚ) / A i) ne
    obtain ⟨ks,kp⟩ := mem_filter.mp hk
    have bound (i : ℕ) (hi : i ∈ s) : A k * B i ≤ B k * A i := by
      rcases lt_trichotomy (A i) 0 with neg | eq | pos
      · linarith only [cross k ks i hi kp neg]
      · rw [eq,mul_zero]
        exact mul_nonpos_of_nonneg_of_nonpos kp.le (vertical i hi eq)
      · have h := (div_le_div_iff₀ (by exact_mod_cast pos : (0:ℚ)<A i)
            (by exact_mod_cast kp : (0:ℚ)<A k)).mp (best i (mem_filter.mpr ⟨hi,pos⟩))
        rw [mul_comm]
        exact_mod_cast h
    have all := sum_le_sum bound
    rw [←mul_sum,←mul_sum,total,mul_zero] at all
    exact nonpos_of_mul_nonpos_right all kp
  · have nn (i : ℕ) (hi : i∈s) : A i ≤ 0 := by
      by_contra! h
      exact ne ⟨i,mem_filter.mpr ⟨hi,h⟩⟩
    exact sum_nonpos fun i hi => vertical i hi ((sum_eq_zero_iff_of_nonpos nn).mp total i hi)

end StirlingBoxes.OmissionCenter
#print axioms StirlingBoxes.OmissionCenter.column_one_concave
#print axioms StirlingBoxes.OmissionCenter.column_one_unimodal
#print axioms StirlingBoxes.OmissionCenter.column_one_central_parity
#print axioms StirlingBoxes.OmissionCenter.column_one_omissions
#print axioms StirlingBoxes.OmissionCenter.parity_of_omission_payment
