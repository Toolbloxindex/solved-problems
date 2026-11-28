module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace ArmstrongOddTwo

/-- The left column height, less one, moves right on alternate late ranks. -/
def offset (n rank : ℕ) : ℕ := (rank + 2 - 2 * n) / 2

def pairAt (n chain step : ℕ) : ℕ × ℕ :=
  let rank := 2 * chain + step
  let short := chain + offset n rank
  (short, rank - short)

theorem pairAt_ordered (n t k : ℕ) (ht : t < n) (hk : k ≤ 2 * n) :
    (pairAt n t k).1 ≤ (pairAt n t k).2 ∧ (pairAt n t k).2 < 2 * n := by
  unfold pairAt offset
  dsimp
  omega

theorem pairAt_rank (n t k : ℕ) (ht : t < n) (hk : k ≤ 2 * n) :
    (pairAt n t k).1 + (pairAt n t k).2 = 2 * t + k := by
  have ordered := (pairAt_ordered n t k ht hk).1
  unfold pairAt at ordered ⊢
  dsimp at ordered ⊢
  omega

theorem pairAt_step (n t k : ℕ) (ht : t < n) (hk : k + 1 ≤ 2 * n) :
    let p := pairAt n t k
    pairAt n t (k + 1) = (p.1 + 1,p.2) ∨
      pairAt n t (k + 1) = (p.1,p.2 + 1) := by
  have ordered := (pairAt_ordered n t k ht (by omega)).1
  unfold pairAt offset at ordered ⊢
  dsimp at ordered ⊢
  simp only [Prod.mk.injEq]
  omega

theorem pair_partition (n i j : ℕ) (hij : i ≤ j) (hj : j < 2 * n) :
    ∃! p : Fin n × Fin (2 * n + 1), pairAt n p.1.val p.2.val = (i,j) := by
  let t := i - offset n (i+j)
  let k := i + j - 2*t
  have ho : offset n (i+j) ≤ i := by unfold offset; omega
  have ht : t < n := by dsimp [t,offset]; omega
  have hk : k < 2 * n + 1 := by dsimp [k,t,offset]; omega
  have rank : 2*t+k = i+j := by dsimp [k,t]; omega
  have member : pairAt n t k = (i,j) := by
    unfold pairAt
    rw [rank]
    simp only [Prod.mk.injEq]
    dsimp [t]
    omega
  refine ⟨(⟨t,ht⟩,⟨k,hk⟩), member, ?_⟩
  intro p h
  have pr := pairAt_rank n p.1.val p.2.val p.1.isLt (by omega)
  rw [h] at pr
  change i + j = 2 * p.1.val + p.2.val at pr
  apply Prod.ext
  · apply Fin.ext
    have he := congrArg Prod.fst h
    change p.1.val + offset n (2*p.1.val+p.2.val) = i at he
    rw [← pr] at he
    dsimp [t]
    omega
  · apply Fin.ext
    have he := congrArg Prod.fst h
    change p.1.val + offset n (2*p.1.val+p.2.val) = i at he
    rw [← pr] at he
    dsimp [k,t]
    omega


/-- Exactly two columns, each positive, in the source's tilted coordinates. -/
def Diagram (n : ℕ) (y : Fin (2*n) → ℕ) : Prop :=
  Antitone y ∧ ∀ h, h.val = 0 → y h = 2

def fromPair (n i j : ℕ) (h : Fin (2*n)) : ℕ :=
  (if h.val ≤ i then 1 else 0) + (if h.val ≤ j then 1 else 0)

private theorem fromPair_mem (n i j : ℕ) : Diagram n (fromPair n i j) := by
  constructor
  · intro r s hrs
    change r.val ≤ s.val at hrs
    unfold fromPair
    split <;> split <;> split <;> split <;> omega
  · intro h hz
    simp [fromPair, hz]

private theorem threshold_one {n i j : ℕ} (order : i ≤ j) (h : Fin (2*n)) :
    1 ≤ fromPair n i j h ↔ h.val ≤ j := by
  unfold fromPair
  split <;> split <;> omega

private theorem threshold_two {n i j : ℕ} (order : i ≤ j) (h : Fin (2*n)) :
    2 ≤ fromPair n i j h ↔ h.val ≤ i := by
  unfold fromPair
  split <;> split <;> omega

private theorem fromPair_inj {n i j u v : ℕ} (ij : i ≤ j) (uv : u ≤ v)
    (hj : j < 2*n) (hv : v < 2*n) (eq : fromPair n i j = fromPair n u v) :
    i = u ∧ j = v := by
  have short (h : Fin (2*n)) : h.val ≤ i ↔ h.val ≤ u := by
    rw [← threshold_two ij, ← threshold_two uv, eq]
  have tall (h : Fin (2*n)) : h.val ≤ j ↔ h.val ≤ v := by
    rw [← threshold_one ij, ← threshold_one uv, eq]
  exact ⟨Nat.le_antisymm ((short ⟨i,by omega⟩).mp (Nat.le_refl _))
      ((short ⟨u,by omega⟩).mpr (Nat.le_refl _)),
    Nat.le_antisymm ((tall ⟨j,hj⟩).mp (Nat.le_refl _))
      ((tall ⟨v,hv⟩).mpr (Nat.le_refl _))⟩

private theorem threshold_top {m : ℕ} {y : Fin m → ℕ} (anti : Antitone y)
    (k : ℕ) (some_row : ∃ h, k ≤ y h) :
    ∃ top : Fin m, ∀ h : Fin m, k ≤ y h ↔ h ≤ top := by
  classical
  let support := Finset.univ.filter fun h => k ≤ y h
  obtain ⟨h, hh⟩ := some_row
  have nonempty : support.Nonempty := ⟨h, by simp [support,hh]⟩
  have atTop : k ≤ y (support.max' nonempty) := by
    have mem := Finset.max'_mem support nonempty
    simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and] using mem
  refine ⟨support.max' nonempty, fun r => ⟨?_,?_⟩⟩
  · intro hr
    exact Finset.le_max' support _ (by simp [support,hr])
  · intro hr
    exact atTop.trans (anti hr)

private theorem fromPair_surj {n : ℕ} (hn : 0 < n) {y : Fin (2*n) → ℕ}
    (valid : Diagram n y) :
    ∃ i j, i ≤ j ∧ j < 2*n ∧ fromPair n i j = y := by
  let zero : Fin (2*n) := ⟨0,by omega⟩
  have first : y zero = 2 := valid.2 zero rfl
  obtain ⟨i,hi⟩ := threshold_top valid.1 2 ⟨zero,by omega⟩
  obtain ⟨j,hj⟩ := threshold_top valid.1 1 ⟨zero,by omega⟩
  have hi₂ := (hi i).mpr (le_refl i)
  have order : i ≤ j := (hj i).mp (by omega)
  refine ⟨i.val,j.val,order,j.isLt,?_⟩
  funext r
  have maxTwo : y r ≤ 2 := by
    have cmp := valid.1 (show zero ≤ r by exact Nat.zero_le _)
    rwa [first] at cmp
  have h2 := hi r
  have h1 := hj r
  change (2 ≤ y r ↔ r.val ≤ i.val) at h2
  change (1 ≤ y r ↔ r.val ≤ j.val) at h1
  unfold fromPair
  split <;> split <;> omega

/-- An increase of one whole rank in the tilted order. -/
def UnitStep {n : ℕ} (before after : Fin (2*n) → ℕ) : Prop :=
  ∃ row, ∀ h, after h = before h + if h = row then 1 else 0

private theorem fromPair_step_left {n i j : ℕ} (hi : i + 1 < 2*n) :
    UnitStep (fromPair n i j) (fromPair n (i+1) j) := by
  refine ⟨⟨i+1,hi⟩, fun h => ?_⟩
  have eq : h = (⟨i+1,by omega⟩ : Fin (2*n)) ↔ h.val = i+1 := Fin.ext_iff
  simp only [eq]
  by_cases atRow : h.val = i+1
  · simp [fromPair, atRow, Nat.add_comm]
  · have same : h.val ≤ i+1 ↔ h.val ≤ i := by omega
    simp [fromPair, atRow, same]

private theorem fromPair_step_right {n i j : ℕ} (hj : j + 1 < 2*n) :
    UnitStep (fromPair n i j) (fromPair n i (j+1)) := by
  refine ⟨⟨j+1,hj⟩, fun h => ?_⟩
  have eq : h = (⟨j+1,by omega⟩ : Fin (2*n)) ↔ h.val = j+1 := Fin.ext_iff
  simp only [eq]
  by_cases atRow : h.val = j+1
  · simp [fromPair, atRow, Nat.add_comm]
  · have same : h.val ≤ j+1 ↔ h.val ≤ j := by omega
    simp [fromPair, atRow, same]

/-- Conjecture 10.2 for every odd a = 2n + 1 with c = 2 and preceding endpoint 1. -/
theorem c2_ribbon_partition (n : ℕ) (hn : 0 < n) :
    ∃ ribbons : Fin n → Fin (2*n+1) → (Fin (2*n) → ℕ),
      (∀ t k, Diagram n (ribbons t k)) ∧
      (∀ y, Diagram n y → ∃! p : Fin n × Fin (2*n+1), ribbons p.1 p.2 = y) ∧
      (∀ t u v, v.val = u.val + 1 → UnitStep (ribbons t u) (ribbons t v)) := by
  let ribbons := fun (t : Fin n) (k : Fin (2*n+1)) =>
    fromPair n (pairAt n t.val k.val).1 (pairAt n t.val k.val).2
  refine ⟨ribbons, (fun _ _ => fromPair_mem ..), ?_, ?_⟩
  · intro y valid
    obtain ⟨i,j,order,bound,eq⟩ := fromPair_surj hn valid
    obtain ⟨p,member,unique⟩ := pair_partition n i j order bound
    refine ⟨p,by simpa only [ribbons,member] using eq,?_⟩
    intro q hq
    have ordered := pairAt_ordered n q.1.val q.2.val q.1.isLt (by omega)
    have cmp := fromPair_inj ordered.1 order ordered.2 bound (hq.trans eq.symm)
    exact unique q (Prod.ext cmp.1 cmp.2)
  · intro t u v next
    have step := pairAt_step n t.val u.val t.isLt (by omega)
    rw [← next] at step
    have bound := pairAt_ordered n t.val v.val t.isLt (by omega)
    rcases step with h | h
    · rw [h] at bound
      simpa only [ribbons,h] using
        (fromPair_step_left (n := n) (i := (pairAt n t.val u.val).1) (j := (pairAt n t.val u.val).2) (by omega))
    · rw [h] at bound
      simpa only [ribbons,h] using
        (fromPair_step_right (n := n) (i := (pairAt n t.val u.val).1)
          (j := (pairAt n t.val u.val).2) (by omega))

end ArmstrongOddTwo
