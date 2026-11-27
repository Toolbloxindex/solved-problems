module

public import OmissionCenter

@[expose] public section

namespace StirlingBoxes.OmissionCenter
open Finset StirlingRecurrence

/-- The sign can change from positive to negative only. Zeros are unrestricted. -/
private def NoUp (f : Seq) := ∀ x y : ℤ, x≤y → f x<0 → f y≤0

private theorem noUp_box {f : Seq} (hf : NoUp f) (k : ℕ) : NoUp (box k f) := by
  intro x y xy neg
  by_contra! pos
  obtain ⟨j,hj,hneg⟩ : ∃ j ∈ range (2*k+1), f (x-j)<0 := by
    by_contra! h
    exact (not_lt_of_ge (sum_nonneg h)) neg
  obtain ⟨l,hl,hpos⟩ : ∃ l ∈ range (2*k+1), 0<f (y-l) := by
    by_contra! h
    exact (not_lt_of_ge (sum_nonpos h)) pos
  have jl := mem_range.mp hl
  have step (z : ℤ) (lo : x≤z) (hi : z<y) : box k f (z+1)≤box k f z := by
    have enter := hf (x-j) (z+1) (by omega) hneg
    have leave : 0≤f (z-2*k) := by
      by_contra! h
      exact (not_lt_of_ge (hf _ _ (by omega) h)) hpos
    have := slide k f z
    omega
  obtain ⟨m,eq⟩ := Int.le.dest xy
  have fall (s : ℕ) (hs : s≤m) : box k f (x+s)≤box k f x := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Nat.cast_succ,←add_assoc]
      exact (step _ (by omega) (by omega)).trans (ih (by omega))
  have last := fall m le_rfl
  rw [eq] at last
  omega

/-- The product of the common windows, acting by convolution. -/
private def common (i j : ℕ) : ℕ → Seq → Seq
  | 0, f => f
  | n+1, f => if n=i ∨ n=j then common i j n f else box n (common i j n f)

private theorem common_box (i j n k : ℕ) (f : Seq) :
    common i j n (box k f)=box k (common i j n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [common]; split
    · exact ih
    · rw [ih]; exact funext (box_comm n k _)

private theorem restore (n i j : ℕ) :
    omitted n i=common i j n (if j<n ∧ j≠i then box j unit else unit) := by
  induction n with
  | zero => simp [omitted,common]
  | succ n ih =>
    by_cases ei : n=i
    · subst i
      have eq : (j<n+1 ∧ j≠n) ↔ (j<n ∧ j≠n) := by omega
      simpa only [omitted,common,eq,ite_true,true_or] using ih
    · by_cases ej : n=j
      · subst j
        simp only [omitted,common,false_or,ite_false,ite_true,lt_add_one,
          ne_eq,ei,not_false_eq_true,and_self,ite_true,common_box]
        simpa using congrArg (box n) ih
      · have eq : (j<n+1 ∧ j≠i) ↔ (j<n ∧ j≠i) := by omega
        simp only [omitted,common,eq,ei,ej,or_self,ite_false,ih]

private theorem common_sym (i j n : ℕ) (f : Seq) :
    common j i n f=common i j n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [common,or_comm,ih]

private def tilt (s a b : ℤ) (f : Seq) : Seq := fun t => a*f (t+s)-b*f t

private theorem tilt_box (s a b : ℤ) (f : Seq) (k : ℕ) :
    tilt s a b (box k f)=box k (tilt s a b f) := by
  funext t
  simp only [tilt,box,sum_sub_distrib,←mul_sum]
  congr 2
  apply sum_congr rfl
  intro j _
  congr 1
  omega

private def kernel (k : ℕ) : Seq := fun t => if 0≤t ∧ t≤2*k then 1 else 0

private theorem box_unit_kernel (k : ℕ) : box k unit=kernel k := by
  funext t
  unfold box unit kernel
  by_cases h : 0≤t ∧ t≤2*k
  · rw [ite_eq_left h, sum_eq_single t.toNat]
    · simp [Int.toNat_of_nonneg h.1]
    · intro j hj ne
      simp [show t-(j:ℤ)≠0 by omega]
    · intro no
      exact (no (mem_range.mpr (by omega))).elim
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro j hj
    have := mem_range.mp hj
    simp [show t-(j:ℤ)≠0 by omega]

private theorem seed_kernel (i j n : ℕ) :
    (if j<n ∧ j≠i then box j unit else unit) =
      kernel (if j<n ∧ j≠i then j else 0) := by
  split
  · exact box_unit_kernel _
  · funext t
    by_cases h : t=0
    · simp [unit,kernel,h]
    · simp [unit,kernel,h,show ¬(0≤t ∧ t≤0) by omega]

private theorem kernel_noUp (i j : ℕ) (s a b u v : ℤ) (hs : 0≤s)
    (ha : 0≤a) (hab : a≤b) (hu : 0≤u) (hv : 0≤v) :
    NoUp (tilt s a b (fun z => u*kernel i z+v*kernel j z)) := by
  let F := fun z => u*kernel i z+v*kernel j z
  have nn (z : ℤ) : 0≤F z := by dsimp [F,kernel]; split <;> split <;> omega
  have anti (k : ℕ) (z : ℤ) (hz : 0≤z) : kernel k (z+s)≤kernel k z := by
    unfold kernel; split <;> split <;> omega
  intro x y xy neg
  change a*F (x+s)-b*F x<0 at neg
  change a*F (y+s)-b*F y≤0
  have hx : 0≤x := by
    by_contra! h
    have zero : F x=0 := by simp [F,kernel,not_le.mpr h]
    rw [zero,mul_zero,sub_zero] at neg
    exact (not_lt_of_ge (mul_nonneg ha (nn _))) neg
  have mono : F (y+s)≤F y := add_le_add
    (mul_le_mul_of_nonneg_left (anti i y (by omega)) hu)
    (mul_le_mul_of_nonneg_left (anti j y (by omega)) hv)
  exact sub_nonpos.mpr ((mul_le_mul_of_nonneg_left mono ha).trans
    (mul_le_mul_of_nonneg_right hab (nn y)))

private theorem common_noUp (i j n : ℕ) (s a b u v : ℤ) (f g : Seq)
    (H : NoUp (tilt s a b (fun z => u*f z+v*g z))) :
    NoUp (tilt s a b (fun z => u*common i j n f z+v*common i j n g z)) := by
  induction n with
  | zero => exact H
  | succ n ih =>
    simp only [common]
    split
    · exact ih
    · have eq : (fun z => u*box n (common i j n f) z+v*box n (common i j n g) z) =
          box n (fun z => u*common i j n f z+v*common i j n g z) := by
        funext z; simp only [box,sum_add_distrib,←mul_sum]
      rw [eq,tilt_box]
      exact noUp_box ih n

private theorem pair_noUp (n i j : ℕ) (s a b u v : ℤ) (hs : 0≤s)
    (ha : 0≤a) (hab : a≤b) (hu : 0≤u) (hv : 0≤v) :
    NoUp (tilt s a b (fun z => u*omitted n i z+v*omitted n j z)) := by
  have I := restore n i j
  have J := restore n j i
  rw [seed_kernel] at I J
  rw [common_sym j i] at I
  rw [I,J]
  exact common_noUp _ _ _ _ _ _ _ _ _ _ (kernel_noUp _ _ _ _ _ _ _ hs ha hab hu hv)

/-- For any stride, ordered outside coefficients suffice on the increasing
side of column one. In particular this includes both source parity classes. -/
theorem column_one_rising_gap (r : ℕ) (d s : ℤ) (hs : 0≤s)
    (rise : cb (r+1) 1 (d-s)≤cb (r+1) 1 (d+s)) :
    cb (r+1) 1 (d-s)*cb (r+1) 1 (d+s)≤cb (r+1) 1 d^2 := by
  let f := cb (r+1) 1
  let a := f (d-s)+f d
  let b := f d+f (d+s)
  have nn (x : ℤ) : 0≤f x := by
    change 0≤coeff true (r+1) 1 x
    rw [source true _ _ r (by omega)]
    exact F_nn ..
  have ha : 0≤a := add_nonneg (nn _) (nn _)
  have hab : a≤b := by change f (d-s)+f d≤f d+f (d+s); linarith only [rise]
  let L := fun i => a*omitted (r+1) i d-b*omitted (r+1) i (d-s)
  let R := fun i => a*omitted (r+1) i (d+s)-b*omitted (r+1) i d
  let S := range (r+1)
  have ls : ∑ i ∈ S,L i=a*f d-b*f (d-s) := by
    simp only [S,L,sum_sub_distrib,←mul_sum,column_one_omissions,f]
  have rs : ∑ i ∈ S,R i=a*f (d+s)-b*f d := by
    simp only [S,R,sum_sub_distrib,←mul_sum,column_one_omissions,f]
  let A := fun i => L i+R i
  have tot : ∑ i ∈ S,A i=0 := by
    simp only [A,sum_add_distrib,ls,rs,a,b]; ring
  have balance (i j : ℕ) (u v : ℤ) (hu : 0≤u) (hv : 0≤v)
      (eq : u*A i+v*A j=0) : u*R i+v*R j≤0 := by
    by_contra! pos
    have neg : u*L i+v*L j<0 := by dsimp only [A] at eq; linarith only [eq,pos]
    have P := pair_noUp (r+1) i j s a b u v hs ha hab hu hv
      (d-s) d (by omega)
    simp only [tilt,sub_add_cancel] at P
    dsimp only [L] at neg
    dsimp only [R] at pos
    have H := P (by linarith only [neg])
    linarith only [pos,H]
  have bound := balanced_sum S A R tot (fun i _ eq => by
    simpa using balance i i 1 0 (by decide) le_rfl (by simp [eq]))
    (fun i _ j _ pi nj => balance i j (-A j) (A i) (by omega) pi.le (by ring))
  rw [rs] at bound
  dsimp only [a,b] at bound
  change f (d-s)*f (d+s)≤f d^2
  linarith only [bound]

/-- The published stride-two inequality throughout the lower side and
central band, with a bound on degree independent of coefficient comparisons. -/
theorem column_one_lower_parity (r : ℕ) (d : ℤ)
    (low : d≤center r ∨ d+1<center (r+1)) :
    cb (r+1) 1 (d-2)*cb (r+1) 1 (d+2)≤cb (r+1) 1 d^2 := by
  by_cases le : d≤center r
  · apply column_one_rising_gap r d 2 (by decide)
    exact column_one_left_pair r _ _ (by omega) (by omega)
  · exact column_one_central_parity r d (by omega) (low.resolve_left le)

end StirlingBoxes.OmissionCenter
#print axioms StirlingBoxes.OmissionCenter.column_one_rising_gap
#print axioms StirlingBoxes.OmissionCenter.column_one_lower_parity
