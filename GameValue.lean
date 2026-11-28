module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! A comparison for Node-Kayles with two identical attached branches.
A root-preserving move in an arm can also leave a detached game of nimber d. -/
namespace KaylesXor

@[simp] theorem cancel_left (x y : Nat) : x ^^^ (x ^^^ y) = y := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

@[simp] theorem cancel_right (x y : Nat) : (x ^^^ y) ^^^ y = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

end KaylesXor

namespace KaylesPair

/-- An option relation has mex n if n is unavailable and every smaller
nimber occurs. This description needs no bound on the ambient nimbers. -/
def IsMex (option : ℕ → Prop) (n : ℕ) :=
  (¬option n) ∧ ∀ k<n, option k

/-- X is a surviving host with its attachment vertex. An arm state may
include detached components. The empty arm has no root or quiet moves. -/
structure Rules (Host Arm : Type) where
  empty : Arm
  sizeH : Host → ℕ
  sizeA : Arm → ℕ
  hostMove : Host → Host → Prop
  armMove : Arm → Arm → ℕ → Prop
  host_lt : ∀ {h h'}, hostMove h h' → sizeH h' < sizeH h
  arm_lt : ∀ {a a' d}, armMove a a' d → sizeA a' < sizeA a
  empty_quiet : ∀ a d, ¬armMove empty a d
  /-- Common root-removing host options in an identical pair. -/
  hostExit : Host → ℕ → Prop
  /-- Options when an extra branch root is selected in an identical pair. -/
  rootExit : Host → Arm → ℕ → Prop
  empty_exit : ∀ h k, ¬rootExit h empty k

/-- The successor option relation at an identical pair. Disjoint identical
tails cancel when a host move removes the common root. -/
def Options {H A : Type} (R : Rules H A) (V : H → A → A → ℕ)
    (h : H) (a : A) (k : ℕ) :=
  R.hostExit h k ∨ R.rootExit h a k ∨
  (∃ h', R.hostMove h h' ∧ V h' a a=k) ∨
  ∃ b d, R.armMove a b d ∧ (V h b a ^^^ d=k ∨ V h a b ^^^ d=k)

/-- If every possible branch-root option differs from the bare host value,
the two attached copies cancel. Only the two opposite responses on unequal
arms are needed in addition to the paired mex equation. -/
theorem pair_cancels {H A : Type} (R : Rules H A) (V : H → A → A → ℕ)
    (mex : ∀ h a, IsMex (Options R V h a) (V h a a))
    (leftReply : ∀ h a b d, R.armMove a b d → V h b a ≠ V h b b ^^^ d)
    (rightReply : ∀ h a b d, R.armMove a b d → V h a b ≠ V h b b ^^^ d)
    (separate : ∀ h a, ¬R.rootExit h a (V h R.empty R.empty))
    (h : H) (a : A) : V h a a=V h R.empty R.empty := by
  suffices aux : ∀ n h a, R.sizeH h + R.sizeA a = n → V h a a=V h R.empty R.empty by
    exact aux _ h a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro h a measure
    have host_eq {j} (move : R.hostMove h j) :
        V j a a=V j R.empty R.empty := ih _ (by have := R.host_lt move; omega) j a rfl
    have arm_eq {b d} (move : R.armMove a b d) :
        V h b b=V h R.empty R.empty := ih _ (by have := R.arm_lt move; omega) h b rfl
    have small := mex h R.empty
    have big := mex h a
    have liftOld {k} (opt : Options R V h R.empty k) : Options R V h a k := by
      rcases opt with common | no | ⟨j,m,e⟩ | ⟨b,d,m,_⟩
      · exact Or.inl common
      · exact (R.empty_exit h k no).elim
      · exact Or.inr (Or.inr (Or.inl ⟨j,m,(host_eq m).trans e⟩))
      · exact (R.empty_quiet b d m).elim
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro less
      have opt := big.2 _ less
      rcases opt with common | bad | ⟨j,m,e⟩ | ⟨b,d,m,e|e⟩
      · exact small.1 (Or.inl common)
      · exact separate h a bad
      · exact small.1 (Or.inr (Or.inr (Or.inl ⟨j,m,(host_eq m).symm.trans e⟩)))
      · apply leftReply h a b d m
        rw [arm_eq m,← e,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
      · apply rightReply h a b d m
        rw [arm_eq m,← e,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
    · apply Nat.le_of_not_gt
      intro less
      exact big.1 (liftOld (small.2 _ less))

/-- If the two sets of XOR differences are disjoint, a first player who
selects an extra branch root cannot reach the bare host nimber. -/
theorem spectrum_cancels {H A : Type} (R : Rules H A) (V : H → A → A → ℕ)
    (mex : ∀ h a, IsMex (Options R V h a) (V h a a))
    (leftReply : ∀ h a b d, R.armMove a b d → V h b a ≠ V h b b ^^^ d)
    (rightReply : ∀ h a b d, R.armMove a b d → V h a b ≠ V h b b ^^^ d)
    (deleted : H → ℕ) (deltas : ℕ → Prop)
    (hit : ∀ h a k, R.rootExit h a k → ∃ d, deltas d ∧ k=deleted h ^^^ d)
    (disjoint : ∀ h, ¬deltas (deleted h ^^^ V h R.empty R.empty))
    (h : H) (a : A) : V h a a=V h R.empty R.empty := by
  apply pair_cancels R V mex leftReply rightReply _ h a
  intro j b opt
  obtain ⟨d,hd,e⟩ := hit j b _ opt
  apply disjoint j
  rwa [e,← Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]

/-- Playing inside a module adjacent only to u can supply a prescribed
root-removing option by the mex property inside that module. -/
theorem module_exit (rest j d host : ℕ) (inside outside : ℕ → Prop)
    (localMex : IsMex inside j) (hostMex : IsMex outside host)
    (joins : ∀ v, inside v → outside (rest ^^^ v))
    (lt : j ^^^ d < j) : (rest ^^^ j) ^^^ d ≠ host := by
  have opt := joins _ (localMex.2 _ lt)
  rw [Nat.xor_assoc]
  intro eq
  exact hostMex.1 (eq ▸ opt)

theorem module_fifteen (d : ℕ) (pos : 0<d) (bound : d<16) : 15 ^^^ d < 15 := by
  have table : ∀ i : Fin 15, 15 ^^^ (i.val+1) < 15 := by decide
  have e := table ⟨d-1,by omega⟩
  simpa only [Nat.sub_add_cancel (by omega : 1≤d)] using e

/-- The duplicated endpoint-rooted P4 has just three surviving connected
root types. The root-move change in detached nimber is one in each case. -/
inductive PathArm where | one | two | four
deriving DecidableEq

def detached : PathArm → ℕ
  | .one | .two => 1
  | .four => 0

def afterRoot : PathArm → ℕ
  | .one | .two => 0
  | .four => 1

theorem path_root_delta (a : PathArm) : afterRoot a ^^^ detached a=1 := by cases a <;> decide

/-- A genuine pendant leaf in the host gives an option of precisely the
branch-root exit value, for every surviving arm type. -/
theorem leaf_excludes_exit (host deleted : ℕ) (options : ℕ → Prop)
    (value : IsMex options host) (leaf : options (deleted ^^^ 1)) (a : PathArm) :
    deleted ^^^ (afterRoot a ^^^ detached a) ≠ host := by
  rw [path_root_delta]
  rintro rfl
  exact value.1 leaf

end KaylesPair
#print axioms KaylesPair.pair_cancels
#print axioms KaylesPair.leaf_excludes_exit
#print axioms KaylesPair.spectrum_cancels
#print axioms KaylesPair.module_exit

/-! Finite Node-Kayles with literal closed-neighborhood deletion.
Each position is its finite set of surviving vertices. -/
namespace LiteralKayles
open KaylesPair

def mexBound (s : Finset ℕ) := s.sup id + 1

theorem bound_missing (s : Finset ℕ) : mexBound s ∉ s := by
  intro h
  have ht : mexBound s ≤ s.sup id := Finset.le_sup (f := id) h
  unfold mexBound at ht
  omega

def missing (s : Finset ℕ) := (Finset.range (mexBound s + 1)) \ s

def mex (s : Finset ℕ) : ℕ :=
  (missing s).min' ⟨mexBound s, by simp [missing, bound_missing]⟩

theorem mex_spec (s : Finset ℕ) : IsMex (· ∈ s) (mex s) := by
  have hmem : mex s ∈ missing s := Finset.min'_mem _ _
  obtain ⟨hle, hout⟩ := Finset.mem_sdiff.mp hmem
  have hlt := Finset.mem_range.mp hle
  refine ⟨hout, ?_⟩
  intro k hk
  by_contra habs
  have hm : k ∈ missing s := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),habs⟩
  exact (not_lt_of_ge (Finset.min'_le _ _ hm)) hk

theorem mex_unique {P : ℕ → Prop} {m n : ℕ} (hm : IsMex P m) (hn : IsMex P n) : m=n := by
  rcases lt_trichotomy m n with h|h|h
  · exact (hm.1 (hn.2 _ h)).elim
  · exact h
  · exact (hn.1 (hm.2 _ h)).elim

@[simp] theorem mex_empty : mex ∅ = 0 := by
  apply mex_unique (mex_spec ∅)
  simp [IsMex]

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/-- Delete the selected vertex and every adjacent vertex. -/
def drop (E : V → V → Bool) (s : Finset V) (v : V) :=
  s.filter fun w => w ≠ v ∧ E v w = false

theorem drop_sub (E : V → V → Bool) (s : Finset V) (v : V) : drop E s v ⊆ s :=
  Finset.filter_subset _ _

theorem drop_lt (E : V → V → Bool) (s : Finset V) {v} (hv : v ∈ s) :
    (drop E s v).card < s.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨drop_sub .., ?_⟩
  intro h
  have : v ∈ drop E s v := h.symm ▸ hv
  simp [drop] at this

def eval (E : V → V → Bool) : ℕ → Finset V → ℕ
  | 0, _ => 0
  | n+1, s => mex (s.image fun v => eval E n (drop E s v))

def value (E : V → V → Bool) (s : Finset V) := eval E s.card s

theorem stable (E : V → V → Bool) (n m : ℕ) (s : Finset V)
    (hn : s.card ≤ n) (hm : s.card ≤ m) : eval E n s = eval E m s := by
  induction n generalizing m s with
  | zero =>
    have e : s=∅ := Finset.card_eq_zero.mp (by omega)
    cases m <;> simp [e,eval]
  | succ n ih =>
    cases m with
    | zero =>
      have e : s=∅ := Finset.card_eq_zero.mp (by omega)
      simp [e,eval]
    | succ m =>
      simp only [eval]
      congr 1
      apply Finset.image_congr
      intro v hv
      have hlt := drop_lt E _ hv
      exact ih m _ (by omega) (by omega)

theorem value_eq (E : V → V → Bool) (s : Finset V) :
    value E s = mex (s.image fun v => value E (drop E s v)) := by
  rw [value, stable E s.card (s.card+1) s (by omega) (by omega), eval]
  congr 1
  apply Finset.image_congr
  intro v hv
  have := drop_lt E _ hv
  exact stable E _ _ _ (by omega) (by omega)

theorem value_spec (E : V → V → Bool) (s : Finset V) :
    IsMex (fun k => ∃ v ∈ s, value E (drop E s v) = k) (value E s) := by
  nth_rw 1 [value_eq E s]
  simpa only [Finset.mem_image] using mex_spec (s.image fun v => value E (drop E s v))

theorem move_ne (E : V → V → Bool) {s : Finset V} {v : V} (hv : v ∈ s) :
    value E s ≠ value E (drop E s v) := fun e => (value_spec E s).1 ⟨v,hv,e.symm⟩

theorem value_empty (E : V → V → Bool) : value E ∅ = 0 := rfl

/-- The induced graph on a mapped finite set has the same value. -/
theorem value_map (E : V → V → Bool) (D : W → W → Bool) (f : V ↪ W)
    (pres : ∀ v w, D (f v) (f w) = E v w) (s : Finset V) :
    value D (s.map f) = value E s := by
  induction s using Finset.strongInduction with
  | H s ih =>
    have transfer {v : V} (hv : v∈s) :
        value D (drop D (s.map f) (f v)) = value E (drop E s v) := by
      have he : drop D (s.map f) (f v) = (drop E s v).map f := by
        ext x
        constructor
        · intro h
          obtain ⟨hx,hn,he⟩ := Finset.mem_filter.mp h
          obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hx
          exact Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr
            ⟨hw,fun e => hn (congrArg f e), (pres ..) ▸ he⟩,rfl⟩
        · intro h
          obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp h
          obtain ⟨hw,hn,he⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨w,hw,rfl⟩,
            fun e => hn (f.injective e), (pres ..).trans he⟩
      rw [he]
      apply ih
      exact Finset.ssubset_iff_subset_ne.mpr ⟨drop_sub ..,fun e => (drop_lt E s hv).ne (congrArg Finset.card e)⟩
    apply mex_unique (value_spec D (s.map f))
    obtain ⟨hn,hs⟩ := value_spec E s
    constructor
    · rintro ⟨x,hx,he⟩
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
      exact hn ⟨v,hv,(transfer hv).symm.trans he⟩
    · intro k hk
      obtain ⟨v,hv,he⟩ := hs _ hk
      exact ⟨f v,Finset.mem_map.mpr ⟨v,hv,rfl⟩,(transfer hv).trans he⟩

def Separated (E : V → V → Bool) (s t : Finset V) :=
  ∀ x∈s, ∀ y∈t, x≠y ∧ E x y=false ∧ E y x=false

omit [DecidableEq V] in
theorem Separated.symm {E : V → V → Bool} {s t : Finset V} (h : Separated E s t) :
    Separated E t s := by
  intro y hy x hx
  obtain ⟨hn,he,hd⟩ := h x hx y hy
  exact ⟨Ne.symm hn,hd,he⟩

theorem clear_union {E : V → V → Bool} {s t : Finset V} (h : Separated E s t) {v} (hv : v∈s) :
    drop E (s∪t) v = drop E s v ∪ t := by
  have fixed : drop E t v = t := Finset.filter_eq_self.mpr fun w hw =>
    ⟨Ne.symm (h v hv w hw).1,(h v hv w hw).2.1⟩
  simpa only [drop, Finset.filter_union] using congrArg (drop E s v ∪ ·) fixed

/-- Sprague-Grundy XOR for disjoint graphs with no cross edges. -/
theorem value_union (E : V → V → Bool) (s t : Finset V) (sep : Separated E s t) :
    value E (s∪t) = value E s ^^^ value E t := by
  suffices aux : ∀ n (s t : Finset V), s.card+t.card=n → Separated E s t →
      value E (s∪t) = value E s ^^^ value E t from aux _ s t rfl sep
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro s t measure sep
    have left {v} (hv : v ∈ s) :
        value E (drop E (s∪t) v) = value E (drop E s v) ^^^ value E t := by
      rw [clear_union sep hv]
      exact ih _ (by have := drop_lt E s hv; omega) _ _ rfl
        (fun x hx y hy => sep x (drop_sub _ _ _ hx) y hy)
    have right {v} (hv : v ∈ t) :
        value E (drop E (s∪t) v) = value E s ^^^ value E (drop E t v) := by
      rw [Finset.union_comm s t, clear_union sep.symm hv, Finset.union_comm]
      exact ih _ (by have := drop_lt E t hv; omega) _ _ rfl
        (fun x hx y hy => sep x hx y (drop_sub _ _ _ hy))
    apply mex_unique (value_spec E (s∪t))
    constructor
    · rintro ⟨v,hv,he⟩
      rcases Finset.mem_union.mp hv with hv|hv
      · rw [left hv] at he
        exact move_ne E hv (by simpa [Nat.xor_assoc] using (congrArg (· ^^^ value E t) he.symm))
      · rw [right hv] at he
        exact move_ne E hv (by simpa [← Nat.xor_assoc] using (congrArg (value E s ^^^ ·) he.symm))
    · intro k hk
      rcases Nat.lt_xor_cases hk with h|h
      · obtain ⟨v,hv,e⟩ := (value_spec E s).2 _ h
        exact ⟨v,Finset.mem_union_left _ hv,by rw [left hv,e,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]⟩
      · obtain ⟨v,hv,e⟩ := (value_spec E t).2 _ h
        exact ⟨v,Finset.mem_union_right _ hv,by rw [right hv,e,Nat.xor_comm k,← Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]⟩

end LiteralKayles
#print axioms LiteralKayles.value_union
