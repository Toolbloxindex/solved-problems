module

public import GameValue
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace LiteralKayles
variable {V : Type} [DecidableEq V]

/-- A hub is superfluous if playing it never reaches the value obtained by erasing it.
Only positions reachable while retaining the hub are needed. -/
theorem erase_hub_of_quiet (E : V → V → Bool) (u : V) (P : Finset V → Prop)
    (quiet : ∀ s, P s → ∀ v∈s, v ≠ u → u ∈ drop E s v → P (drop E s v))
    (hub : ∀ s, P s → u ∈ s → value E (drop E s u) ≠ value E (s.erase u))
    (s : Finset V) (hs : P s) : value E s = value E (s.erase u) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hu : u ∈ s
    · have transfer (v) (hv : v∈s) (hn : v≠u) :
          value E (drop E s v) = value E (drop E (s.erase u) v) := by
        have comm : (drop E s v).erase u = drop E (s.erase u) v := by
          ext w
          simp only [drop,Finset.mem_erase,Finset.mem_filter]
          tauto
        rw [← comm]
        by_cases alive : u ∈ drop E s v
        · apply ih (drop E s v) (Finset.ssubset_iff_subset_ne.mpr
            ⟨drop_sub ..,fun e => (drop_lt E s hv).ne (congrArg Finset.card e)⟩)
          exact quiet s hs v hv hn alive
        · rw [Finset.erase_eq_of_notMem alive]
      apply mex_unique (value_spec E s)
      constructor
      · rintro ⟨v,hv,eq⟩
        by_cases hn : v=u
        · exact hub s hs hu (hn ▸ eq)
        · exact (value_spec E (s.erase u)).1 ⟨v,Finset.mem_erase.mpr ⟨hn,hv⟩,
              (transfer v hv hn).symm.trans eq⟩
      · intro k hk
        obtain ⟨v,hv,e⟩ := (value_spec E (s.erase u)).2 _ hk
        obtain ⟨hn,hv⟩ := Finset.mem_erase.mp hv
        exact ⟨v,hv,(transfer _ hv hn).trans e⟩
    · rw [Finset.erase_eq_of_notMem hu]

end LiteralKayles
#print axioms LiteralKayles.erase_hub_of_quiet

namespace LiteralKayles.Erasure

/-- Finite live board. The ambient vertex type may be infinite. -/
structure Rooted where
  V : Type
  eqV : DecidableEq V
  E : V → V → Bool
  u : V
  board : Finset V
  live : u ∈ board

attribute [instance] Rooted.eqV

inductive Reach (H : Rooted) (permitted : H.V → Prop) : Finset H.V → Prop
  | start : Reach H permitted H.board
  | move {s v} : Reach H permitted s → v ∈ s → permitted v → Reach H permitted (drop H.E s v)

def Safe (H : Rooted) (v : H.V) : Prop := v ≠ H.u ∧ H.E v H.u = false

def quiet (H : Rooted) := Reach H (Safe H)

theorem quiet_live {H : Rooted} {s} (q : quiet H s) : H.u ∈ s := by
  induction q with
  | start => exact H.live
  | move _ _ ok ih => exact Finset.mem_filter.mpr ⟨ih, Ne.symm ok.1,ok.2⟩

def discrepancy (H : Rooted) (s : Finset H.V) :=
  value H.E (s.erase H.u) ^^^ value H.E (drop H.E s H.u)

def hostSet (H : Rooted) (d : ℕ) : Prop :=
  ∃ s, quiet H s ∧ discrepancy H s = d

def armSet (A : Rooted) (d : ℕ) : Prop :=
  ∃ s, Reach A (· ≠ A.u) s ∧ value A.E s ^^^ value A.E (s.erase A.u) = d

/-- Exact erasure at all quiet followers is equivalent to omission of zero. -/
theorem hereditary_iff (H : Rooted) :
    (∀ s, quiet H s → value H.E s = value H.E (s.erase H.u)) ↔ ¬hostSet H 0 := by
  constructor
  · intro eq ⟨s,q,zero⟩
    apply move_ne H.E (quiet_live q)
    rw [eq s q]
    exact Nat.xor_eq_zero_iff.mp zero
  · intro absent s q
    apply erase_hub_of_quiet H.E H.u (quiet H) _ _ s q
    · intro t reach v hv hn hu
      exact Reach.move reach hv ⟨hn,(Finset.mem_filter.mp hu).2.2⟩
    · intro t reach _ eq
      exact absent ⟨t,reach,Nat.xor_eq_zero_iff.mpr eq.symm⟩

end LiteralKayles.Erasure

namespace LiteralKayles.Erasure
open Sum
variable (H A : Rooted)

/-- Attach by the single edge between the two roots, keeping the host root. -/
def joined : H.V ⊕ A.V → H.V ⊕ A.V → Bool
  | inl v, inl w => H.E v w
  | inr v, inr w => A.E v w
  | inl v, inr w | inr w, inl v => decide (v=H.u ∧ w=A.u)

def attach : Rooted where
  V := H.V ⊕ A.V
  eqV := inferInstance
  E := joined H A
  u := inl H.u
  board := H.board.disjSum A.board
  live := Finset.inl_mem_disjSum.mpr H.live

theorem drop_l (s : Finset H.V) (t : Finset A.V) (v : H.V) :
    drop (joined H A) (s.disjSum t) (inl v) =
    (drop H.E s v).disjSum (if v=H.u then t.erase A.u else t) := by
  ext (x|x) <;> by_cases hv : v=H.u <;> simp [drop,joined,hv,and_comm]

theorem drop_r (s : Finset H.V) (t : Finset A.V) (v : A.V) :
    drop (joined H A) (s.disjSum t) (inr v) =
    (if v=A.u then s.erase H.u else s).disjSum (drop A.E t v) := by
  ext (x|x) <;> by_cases hv : v=A.u <;> simp [drop,joined,hv,and_comm]

theorem erase_l (s : Finset H.V) (t : Finset A.V) :
    (s.disjSum t).erase (inl H.u) = (s.erase H.u).disjSum t := by
  ext (x|x) <;> simp

theorem detached (s : Finset H.V) (t : Finset A.V) (hu : H.u ∉ s) :
    value (joined H A) (s.disjSum t) = value H.E s ^^^ value A.E t := by
  have split : s.disjSum t = s.map Function.Embedding.inl ∪ t.map Function.Embedding.inr := by
    ext (x|x) <;> simp [Finset.mem_map]
  have sep : Separated (joined H A) (s.map Function.Embedding.inl) (t.map Function.Embedding.inr) := by
    rintro _ hx _ hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w,_,rfl⟩ := Finset.mem_map.mp hy
    have hn : v ≠ H.u := fun e => hu (e ▸ hv)
    simp [joined, hn]
  rw [split,value_union _ _ _ sep,
    value_map H.E (joined H A) Function.Embedding.inl (fun _ _ => rfl),
    value_map A.E (joined H A) Function.Embedding.inr (fun _ _ => rfl)]

theorem joined_discrepancy (s : Finset H.V) (t : Finset A.V) :
    discrepancy (attach H A) (s.disjSum t) =
    discrepancy H s ^^^ (value A.E t ^^^ value A.E (t.erase A.u)) := by
  change value (joined H A) ((s.disjSum t).erase (inl H.u)) ^^^
    value (joined H A) (drop (joined H A) (s.disjSum t) (inl H.u)) = _
  rw [erase_l,drop_l,ite_eq_left rfl,detached H A (s.erase H.u) t (Finset.notMem_erase H.u s),
    detached H A (drop H.E s H.u) (t.erase A.u) (by simp [drop])]
  unfold discrepancy
  ac_rfl

theorem reachable_split {b} (q : quiet (attach H A) b) :
    ∃ s t, quiet H s ∧ Reach A (· ≠ A.u) t ∧ b = s.disjSum t := by
  induction q with
  | start => exact ⟨_,_,.start,.start,rfl⟩
  | @move b v _ hv ok ih =>
    obtain ⟨s,t,hs,ht,rfl⟩ := ih
    cases v with
    | inl v =>
      have safe : Safe H v := ⟨fun h => ok.1 (congrArg inl h),ok.2⟩
      refine ⟨_,_,.move hs (Finset.inl_mem_disjSum.mp hv) safe,ht,?_⟩
      exact (drop_l H A s t v).trans (by rw [ite_eq_right safe.1])
    | inr v =>
      have hn : v ≠ A.u := by
        have e := ok.2
        change decide (H.u=H.u ∧ v=A.u) = false at e
        simpa using e
      refine ⟨_,_,hs,.move ht (Finset.inr_mem_disjSum.mp hv) hn,?_⟩
      exact (drop_r H A s t v).trans (by rw [ite_eq_right hn])

theorem reachable_combine {s t} (hs : quiet H s) (ht : Reach A (· ≠ A.u) t) :
    quiet (attach H A) (s.disjSum t) := by
  have first : quiet (attach H A) (s.disjSum A.board) := by
    induction hs with
    | start => exact .start
    | @move b v _ hv ok ih =>
      have safe : Safe (attach H A) (inl v) :=
        ⟨fun e => ok.1 (Sum.inl.inj e),ok.2⟩
      have next := Reach.move ih (Finset.inl_mem_disjSum.mpr hv) safe
      change quiet (attach H A) (drop (joined H A) _ (inl v)) at next
      exact (congrArg (quiet (attach H A)) ((drop_l H A b A.board v).trans (by rw [ite_eq_right ok.1]))).mp next
  induction ht with
  | start => exact first
  | @move b v _ hv hn ih =>
    have safe : Safe (attach H A) (inr v) := by
      refine ⟨by simp [attach],?_⟩
      change decide (H.u=H.u ∧ v=A.u) = false
      simp [hn]
    have next := Reach.move ih (Finset.inr_mem_disjSum.mpr hv) safe
    change quiet (attach H A) (drop (joined H A) _ (inr v)) at next
    exact (congrArg (quiet (attach H A)) ((drop_r H A s b v).trans (by rw [ite_eq_right hn]))).mp next

/-- The host and the branch may be played independently before the hub is lost. -/
theorem attach_spectrum (d : ℕ) : hostSet (attach H A) d ↔
    ∃ h a, hostSet H h ∧ armSet A a ∧ h ^^^ a = d := by
  constructor
  · rintro ⟨b,hb,eq⟩
    obtain ⟨s,t,hs,ht,rfl⟩ := reachable_split H A hb
    exact ⟨_,_,⟨s,hs,rfl⟩,⟨t,ht,rfl⟩,(joined_discrepancy H A s t).symm.trans eq⟩
  · rintro ⟨_,_,⟨s,hs,rfl⟩,⟨t,ht,rfl⟩,rfl⟩
    exact ⟨_,reachable_combine H A hs ht,joined_discrepancy H A s t⟩

end LiteralKayles.Erasure
#print axioms LiteralKayles.Erasure.attach_spectrum

namespace KaylesRays.FiveMoves
open LiteralKayles LiteralKayles.Erasure Sum

def rayEdge (i j : Fin 5) := decide (i.val+1=j.val ∨ j.val+1=i.val)

abbrev arm (n : Nat) (positive : 0<n) : Rooted where
  V := Fin 5
  eqV := inferInstance
  E := rayEdge
  u := 0
  board := Finset.univ.filter (fun i : Fin 5 => i.val<n)
  live := Finset.mem_filter.mpr ⟨Finset.mem_univ _,positive⟩

def after (H A : Rooted) (i : A.V) : Nat :=
  value (joined H A) (drop (joined H A) (H.board.disjSum A.board) (inr i))

def score (H : Rooted) : Nat := value H.E H.board

private theorem split_tail (H A : Rooted) (p q : Finset A.V)
    (away : A.u ∉ q) (apart : Separated A.E p q) :
    value (joined H A) (H.board.disjSum (p∪q)) =
      value (joined H A) (H.board.disjSum p) ^^^ value A.E q := by
  let emb : A.V ↪ H.V ⊕ A.V := Function.Embedding.inr
  have eq : H.board.disjSum (p∪q) = H.board.disjSum p ∪ q.map emb := by
    ext (x|y) <;> simp [emb,Finset.mem_map]
  have sep : Separated (joined H A) (H.board.disjSum p) (q.map emb) := by
    rintro (x|x) hx y hy
    all_goals obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
    · have ne : v≠A.u := fun h => away (h ▸ hv)
      simp [emb,joined,ne]
    · simpa [emb,joined] using apart _ (Finset.inr_mem_disjSum.mp hx) _ hv
  rw [eq,value_union _ _ _ sep,value_map A.E (joined H A) emb (fun _ _ => rfl)]

private theorem recorded :
    drop rayEdge ((arm 5 (by decide)).board) 1 = ({3,4} : Finset (Fin 5)) ∧
    drop rayEdge ((arm 5 (by decide)).board) 2 = ({0,4} : Finset (Fin 5)) ∧
    drop rayEdge ((arm 5 (by decide)).board) 3 = (arm 2 (by decide)).board ∧
    drop rayEdge ((arm 5 (by decide)).board) 4 = (arm 3 (by decide)).board ∧
    drop rayEdge ((arm 3 (by decide)).board) 1 = ∅ ∧
    drop rayEdge ((arm 3 (by decide)).board) 2 = (arm 1 (by decide)).board := by
  decide +kernel

private theorem empty_arm (H A : Rooted) :
    value (joined H A) (H.board.disjSum ∅) = score H := by
  have eq : H.board.disjSum (∅ : Finset A.V) = H.board.map Function.Embedding.inl := by
    ext (v|v) <;> simp [Finset.mem_map]
  rw [eq]
  exact value_map H.E (joined H A) Function.Embedding.inl (fun _ _ => rfl) H.board

private theorem joined_arm (H : Rooted) (n m : Nat) (hn : 0<n) (hm : 0<m) :
    joined H (arm n hn) = joined H (arm m hm) := by
  funext a b
  cases a <;> cases b <;> rfl

private theorem singleton_arm : (arm 1 (by decide)).board = {0} := by
  decide +kernel

/-- The four genuine hub-preserving moves on a five-vertex ray, before
identifying the positive-leaf two-edge option. The host is arbitrary. -/
theorem five (H : Rooted) :
    after H (arm 5 (by decide)) 1 = score H ^^^ 1 ∧
    after H (arm 5 (by decide)) 2 = score (attach H (arm 1 (by decide))) ^^^ 1 ∧
    after H (arm 5 (by decide)) 3 = score (attach H (arm 2 (by decide))) ∧
    after H (arm 5 (by decide)) 4 = score (attach H (arm 3 (by decide))) := by
  obtain ⟨r₁,r₂,r₃,r₄,_,_⟩ := recorded
  have q₁ : value rayEdge ({3,4} : Finset (Fin 5)) = 1 := by decide +kernel
  have q₂ : value rayEdge ({4} : Finset (Fin 5)) = 1 := by decide +kernel
  have sep₁ : Separated rayEdge ∅ ({3,4} : Finset (Fin 5)) := by
    simp [Separated]
  have sep₂ : Separated rayEdge ({0} : Finset (Fin 5)) ({4} : Finset (Fin 5)) := by
    simp [Separated,rayEdge]
  have rm (i : Fin 5) (hi : i≠0) :
      after H (arm 5 (by decide)) i =
        value (joined H (arm 5 (by decide)))
          (H.board.disjSum (drop rayEdge (arm 5 (by decide)).board i)) := by
    unfold after
    rw [drop_r H (arm 5 (by decide))]
    rw [ite_eq_right hi]
  refine ⟨?_,?_,?_,?_⟩
  · rw [rm 1 (by decide),r₁,←Finset.empty_union ({3,4} : Finset (Fin 5)),
      split_tail H (arm 5 (by decide)) _ _ (by decide) sep₁,empty_arm,q₁]
  · rw [rm 2 (by decide),r₂,show ({0,4} : Finset (Fin 5))={0}∪{4} by decide,
      split_tail H (arm 5 (by decide)) _ _ (by decide) sep₂,q₂,←singleton_arm,
      joined_arm H 5 1 (by decide) (by decide)]
    rfl
  · rw [rm 3 (by decide),r₃,joined_arm H 5 2 (by decide) (by decide)]
    rfl
  · rw [rm 4 (by decide),r₄,joined_arm H 5 3 (by decide) (by decide)]
    rfl

theorem three (H : Rooted) :
    after H (arm 3 (by decide)) 1 = score H ∧
    after H (arm 3 (by decide)) 2 = score (attach H (arm 1 (by decide))) := by
  obtain ⟨_,_,_,_,r₁,r₂⟩ := recorded
  have rm (i : Fin 5) (hi : i≠0) :
      after H (arm 3 (by decide)) i =
        value (joined H (arm 3 (by decide)))
          (H.board.disjSum (drop rayEdge (arm 3 (by decide)).board i)) := by
    unfold after
    rw [drop_r H (arm 3 (by decide))]
    rw [ite_eq_right hi]
  refine ⟨?_,?_⟩
  · rw [rm 1 (by decide),r₁,empty_arm]
  · rw [rm 2 (by decide),r₂,joined_arm H 3 1 (by decide) (by decide)]
    rfl

end KaylesRays.FiveMoves

#print axioms KaylesRays.FiveMoves.five
#print axioms KaylesRays.FiveMoves.three
