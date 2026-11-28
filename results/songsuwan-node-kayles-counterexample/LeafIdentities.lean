import GameValue
import Mathlib.Data.Fintype.Powerset

/-! Attach two endpoint-rooted four-vertex paths by edges from their
zero-labelled vertices to a host vertex. All moves use literal deletion. -/
namespace LiteralKayles.PairedGraph

abbrev Q := Fin 4

def path (i j : Q) : Bool := decide (i.val+1=j.val ∨ j.val+1=i.val)

inductive Vertex (V : Type) where
  | host : V → Vertex V
  | left : Q → Vertex V
  | right : Q → Vertex V
deriving DecidableEq
open Vertex

variable {V : Type} [DecidableEq V]

def adj (E : V → V → Bool) (u : V) : Vertex V → Vertex V → Bool
  | host v, host w => E v w
  | host v, left i | host v, right i => decide (v=u ∧ i=0)
  | left i, host v | right i, host v => decide (v=u ∧ i=0)
  | left i, left j | right i, right j => path i j
  | _,_ => false

def hEmb : V ↪ Vertex V := ⟨host, fun _ _ => Vertex.host.inj⟩
def lEmb : Q ↪ Vertex V := ⟨left, fun _ _ => Vertex.left.inj⟩
def rEmb : Q ↪ Vertex V := ⟨right, fun _ _ => Vertex.right.inj⟩

omit [DecidableEq V] in
@[simp] theorem hEmb_apply (v : V) : hEmb v = host v := rfl
omit [DecidableEq V] in
@[simp] theorem lEmb_apply (i : Q) : (lEmb i : Vertex V) = left i := rfl
omit [DecidableEq V] in
@[simp] theorem rEmb_apply (i : Q) : (rEmb i : Vertex V) = right i := rfl

def board (s : Finset V) (a b : Finset Q) : Finset (Vertex V) :=
  s.map hEmb ∪ a.map lEmb ∪ b.map rEmb

@[simp] theorem host_mem (s : Finset V) (a b : Finset Q) (v : V) :
    host v ∈ board s a b ↔ v ∈ s := by simp [board,Finset.mem_map]

@[simp] theorem left_mem (s : Finset V) (a b : Finset Q) (i : Q) :
    left i ∈ board s a b ↔ i ∈ a := by simp [board,Finset.mem_map]

@[simp] theorem right_mem (s : Finset V) (a b : Finset Q) (i : Q) :
    right i ∈ board s a b ↔ i ∈ b := by simp [board,Finset.mem_map]

theorem drop_host (E : V → V → Bool) (u v : V) (s : Finset V) (a b : Finset Q) :
    drop (adj E u) (board s a b) (host v) =
      board (drop E s v) (if v=u then a.erase 0 else a) (if v=u then b.erase 0 else b) := by
  ext x
  cases x <;> by_cases hv : v=u <;> simp [drop,adj,hv,and_comm]

theorem drop_left (E : V → V → Bool) (u : V) (i : Q) (s : Finset V) (a b : Finset Q) :
    drop (adj E u) (board s a b) (left i) =
      board (if i=0 then s.erase u else s) (drop path a i) b := by
  ext x
  cases x <;> by_cases hi : i=0 <;> simp [drop,adj,hi,and_comm]

theorem drop_right (E : V → V → Bool) (u : V) (i : Q) (s : Finset V) (a b : Finset Q) :
    drop (adj E u) (board s a b) (right i) =
      board (if i=0 then s.erase u else s) a (drop path b i) := by
  ext x
  cases x <;> by_cases hi : i=0 <;> simp [drop,adj,hi,and_comm]

theorem bare (E : V → V → Bool) (u : V) (s : Finset V) :
    value (adj E u) (board s ∅ ∅) = value E s := by
  simpa [board] using value_map E (adj E u) hEmb (fun _ _ => rfl) s

/-- Once u is gone, the literal position splits into three independent games. -/
theorem detached (E : V → V → Bool) (u : V) (s : Finset V) (a b : Finset Q) (hu : u∉s) :
    value (adj E u) (board s a b) = (value E s ^^^ value path a) ^^^ value path b := by
  have sepL : Separated (adj E u) (s.map hEmb) (a.map lEmb) := by
    rintro x hx y hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
    have h : v≠u := fun e => hu (e ▸ hv)
    simp [adj,h]
  have sepR : Separated (adj E u) (s.map hEmb ∪ a.map lEmb) (b.map rEmb) := by
    rintro x hx y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
    rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
      have h : v≠u := fun e => hu (e ▸ hv)
      simp [adj,h]
    · obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hx
      simp [adj]
  rw [board,value_union _ _ _ sepR,value_union _ _ _ sepL,
    value_map E (adj E u) hEmb (fun _ _ => rfl),
    value_map path (adj E u) lEmb (fun _ _ => rfl),
    value_map path (adj E u) rEmb (fun _ _ => rfl)]

/-- Reachable quiet positions permit the full path, prefixes of sizes one
and two, and all subsets with the root absent (including detached pieces). -/
def Good (a : Finset Q) : Prop :=
  0 ∉ a ∨ a = Finset.univ ∨ a = {0,1} ∨ a = {0}

instance (a : Finset Q) : Decidable (Good a) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem good_drop : ∀ (a : Finset Q) (i : Q), Good a → i∈a → i≠0 → Good (drop path a i) := by
  decide

theorem root_change : ∀ (a : Finset Q), Good a → 0∈a →
    (value path (drop path a 0) ^^^ value path a) = 1 := by
  decide

end LiteralKayles.PairedGraph

/-! A pendant leaf at u excludes the only uncopiable move, a play
at the zero vertex of either added branch. -/
namespace LiteralKayles.PairedGraph
open KaylesPair Vertex

variable {V : Type} [DecidableEq V]

abbrev Host (u p : V) := {s : Finset V // u∈s ∧ p∈s}
abbrev Arm := {s : Finset Q // Good s}

/-- A finite host can have arbitrary edges away from the pendant vertex. -/
def LeafAt (E : V → V → Bool) (u p : V) :=
  p≠u ∧ ∀ v, E p v = decide (v=u) ∧ E v p = decide (v=u)

theorem keep_leaf (E : V → V → Bool) {u p v : V} (leaf : LeafAt E u p)
    {s : Finset V} (hp : p∈s) (hu : u∈drop E s v) : p∈drop E s v := by
  obtain ⟨_,hvu,heu⟩ := Finset.mem_filter.mp hu
  have hpne : p≠v := by
    rintro rfl
    rw [(leaf.2 u).1] at heu
    simp at heu
  exact Finset.mem_filter.mpr ⟨hp,hpne,by simp [(leaf.2 v).2,Ne.symm hvu]⟩

theorem value_single (E : V → V → Bool) (v : V) : value E {v} = 1 := by
  rw [value_eq]
  have he : drop E {v} v = ∅ := by ext x; by_cases hx : x=v <;> simp [drop,hx]
  simp [he,value_empty]
  decide

theorem leaf_option (E : V → V → Bool) {u p : V} (leaf : LeafAt E u p)
    {s : Finset V} (hp : p∈s) :
    value E (drop E s p) = value E (s.erase u) ^^^ 1 := by
  have he : drop E s p = (s.erase u).erase p := by
    ext x
    simp [drop,(leaf.2 x).1]
    tauto
  have sep : Separated E ((s.erase u).erase p) {p} := by
    intro x hx y hy
    have hy' := Finset.mem_singleton.mp hy
    subst y
    obtain ⟨hn,hx⟩ := Finset.mem_erase.mp hx
    obtain ⟨hu,_⟩ := Finset.mem_erase.mp hx
    exact ⟨hn,by simp [(leaf.2 x).2,hu],by simp [(leaf.2 x).1,hu]⟩
  have split : (s.erase u).erase p ∪ {p} = s.erase u := by
    ext x
    by_cases hx : x=p <;> simp [hx,leaf.1,hp]
  have e := value_union E _ _ sep
  rw [split,value_single] at e
  rw [he,e,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

def hostMove (E : V → V → Bool) {u p : V} (h j : Host u p) : Prop :=
  ∃ v ∈ h.val, drop E h.val v = j.val

def armMove (a b : Arm) (d : ℕ) : Prop :=
  ∃ i ∈ a.val, i≠0 ∧ drop path a.val i = b.val ∧ d=0

def hostExit (E : V → V → Bool) {u p : V} (h : Host u p) (k : ℕ) : Prop :=
  ∃ v ∈ h.val, u∉drop E h.val v ∧ value E (drop E h.val v) = k

def rootExit (E : V → V → Bool) {u p : V} (h : Host u p) (a : Arm) (k : ℕ) : Prop :=
  0∈a.val ∧ value E (h.val.erase u) ^^^ (value path (drop path a.val 0) ^^^ value path a.val) = k

def rules (E : V → V → Bool) (u p : V) : Rules (Host u p) Arm where
  empty := ⟨∅,by simp [Good]⟩
  sizeH h := h.val.card
  sizeA a := a.val.card
  hostMove := hostMove E
  armMove := armMove
  host_lt := by
    rintro h j ⟨v,hv,e⟩
    rw [← e]
    exact drop_lt _ _ hv
  arm_lt := by
    rintro a b d ⟨i,hi,_,e,_⟩
    rw [← e]
    exact drop_lt _ _ hi
  empty_quiet := by rintro _ _ ⟨i,hi,_⟩; exact Finset.notMem_empty _ hi
  hostExit := hostExit E
  rootExit := rootExit E
  empty_exit := by rintro _ _ ⟨hi,_⟩; exact Finset.notMem_empty _ hi

def pos (E : V → V → Bool) {u p : V} (h : Host u p) (a b : Arm) :=
  value (adj E u) (board h.val a.val b.val)

theorem host_quiet_value (E : V → V → Bool) {u v : V} {s : Finset V} (a b : Finset Q)
    (hu : u∈drop E s v) :
    value (adj E u) (drop (adj E u) (board s a b) (host v)) =
      value (adj E u) (board (drop E s v) a b) := by
  rw [drop_host,ite_eq_right (Ne.symm (Finset.mem_filter.mp hu).2.1),
    ite_eq_right (Ne.symm (Finset.mem_filter.mp hu).2.1)]

theorem host_exit_value (E : V → V → Bool) {u v : V} {s : Finset V} (a : Finset Q)
    (hu : u∉drop E s v) :
    value (adj E u) (drop (adj E u) (board s a a) (host v)) = value E (drop E s v) := by
  rw [drop_host,detached _ _ _ _ _ hu,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem left_exit_value (E : V → V → Bool) (u : V) (s : Finset V) (a : Finset Q) :
    value (adj E u) (drop (adj E u) (board s a a) (left 0)) =
      value E (s.erase u) ^^^ (value path (drop path a 0) ^^^ value path a) := by
  rw [drop_left,ite_eq_left rfl,detached E u (s.erase u) _ _ (Finset.notMem_erase u s),Nat.xor_assoc]

theorem right_exit_value (E : V → V → Bool) (u : V) (s : Finset V) (a : Finset Q) :
    value (adj E u) (drop (adj E u) (board s a a) (right 0)) =
      value E (s.erase u) ^^^ (value path (drop path a 0) ^^^ value path a) := by
  rw [drop_right,ite_eq_left rfl,detached E u (s.erase u) _ _ (Finset.notMem_erase u s),Nat.xor_assoc,
    Nat.xor_comm (value path a)]

theorem options_iff (E : V → V → Bool) {u p : V} (leaf : LeafAt E u p)
    (h : Host u p) (a : Arm) (k : ℕ) :
    Options (rules E u p) (pos E) h a k ↔
      ∃ v ∈ board h.val a.val a.val, value (adj E u) (drop (adj E u) (board h.val a.val a.val) v) = k := by
  constructor
  · rintro (⟨v,hv,hu,e⟩ | ⟨hi,e⟩ | ⟨j,⟨v,hv,hm⟩,e⟩ | ⟨b,d,⟨i,hi,hn,hm,rfl⟩,e⟩)
    · exact ⟨host v,by simpa using hv,(host_exit_value E _ hu).trans e⟩
    · exact ⟨left 0,by simpa using hi,(left_exit_value E ..).trans e⟩
    · have hu : u∈drop E h.val v := hm ▸ j.property.1
      exact ⟨host v,by simpa using hv,by rw [host_quiet_value E _ _ hu,hm]; exact e⟩
    · rcases e with e|e
      · exact ⟨left i,by simpa using hi,by
          rw [drop_left,ite_eq_right hn,hm]; simpa [pos] using e⟩
      · exact ⟨right i,by simpa using hi,by
          rw [drop_right,ite_eq_right hn,hm]; simpa [pos] using e⟩
  · rintro ⟨v,hv,e⟩
    cases v with
    | host v =>
      have hv' := (host_mem ..).mp hv
      by_cases hu : u∈drop E h.val v
      · let j : Host u p := ⟨drop E h.val v,hu,keep_leaf E leaf h.property.2 hu⟩
        exact Or.inr (Or.inr (Or.inl ⟨j,⟨v,hv',rfl⟩,(host_quiet_value E _ _ hu).symm.trans e⟩))
      · exact Or.inl ⟨v,hv',hu,(host_exit_value E _ hu).symm.trans e⟩
    | left i =>
      have hi := (left_mem ..).mp hv
      by_cases hn : i=0
      · subst i
        exact Or.inr (Or.inl ⟨hi,(left_exit_value E ..).symm.trans e⟩)
      · let b : Arm := ⟨drop path a.val i,good_drop _ _ a.property hi hn⟩
        refine Or.inr (Or.inr (Or.inr ⟨b,0,⟨i,hi,hn,rfl,rfl⟩,Or.inl ?_⟩))
        simpa [drop_left,hn,b,pos] using e
    | right i =>
      have hi := (right_mem ..).mp hv
      by_cases hn : i=0
      · subst i
        exact Or.inr (Or.inl ⟨hi,(right_exit_value E ..).symm.trans e⟩)
      · let b : Arm := ⟨drop path a.val i,good_drop _ _ a.property hi hn⟩
        refine Or.inr (Or.inr (Or.inr ⟨b,0,⟨i,hi,hn,rfl,rfl⟩,Or.inr ?_⟩))
        simpa [drop_right,hn,b,pos] using e

/-- In every finite host with a pendant p at u, adding two copies of P4
by edges from u to their respective zero endpoints leaves the nimber unchanged. -/
theorem pendant_p4_pair (E : V → V → Bool) {u p : V} (leaf : LeafAt E u p)
    (s : Finset V) (hu : u∈s) (hp : p∈s) :
    value (adj E u) (board s Finset.univ Finset.univ) = value E s := by
  let R := rules E u p
  have mexR (h : Host u p) (a : Arm) : IsMex (Options R (pos E) h a) (pos E h a a) := by
    have hm := value_spec (adj E u) (board h.val a.val a.val)
    exact ⟨fun hc => hm.1 ((options_iff E leaf ..).mp hc),
      fun k hk => (options_iff E leaf ..).mpr (hm.2 k hk)⟩
  have leftReply (h : Host u p) (a b : Arm) (d : ℕ) (m : armMove a b d) :
      pos E h b a ≠ pos E h b b ^^^ d := by
    obtain ⟨i,hi,hn,hm,rfl⟩ := m
    have hq := move_ne (adj E u) ((right_mem h.val b.val a.val i).mpr hi)
    simpa [drop_right,hn,hm,pos] using hq
  have rightReply (h : Host u p) (a b : Arm) (d : ℕ) (m : armMove a b d) :
      pos E h a b ≠ pos E h b b ^^^ d := by
    obtain ⟨i,hi,hn,hm,rfl⟩ := m
    have hq := move_ne (adj E u) ((left_mem h.val a.val b.val i).mpr hi)
    simpa [drop_left,hn,hm,pos] using hq
  let del (h : Host u p) := value E (h.val.erase u)
  have hit (h : Host u p) (a : Arm) (k : ℕ) (hroot : R.rootExit h a k) :
      ∃ d, d=1 ∧ k=del h ^^^ d := by
    obtain ⟨hi,he⟩ := hroot
    exact ⟨1,rfl,by simpa [del,root_change a.val a.property hi] using he.symm⟩
  have disj (h : Host u p) : ¬ (del h ^^^ pos E h R.empty R.empty = 1) := by
    intro e
    have b : pos E h R.empty R.empty = value E h.val := bare E u h.val
    rw [b] at e
    have ne := move_ne E h.property.2
    rw [leaf_option E leaf h.property.2] at ne
    apply ne
    simpa [del] using congrArg (del h ^^^ ·) e
  let whole : Arm := ⟨Finset.univ,Or.inr (Or.inl rfl)⟩
  exact (spectrum_cancels R (pos E) mexR leftReply rightReply del (·=1) hit disj
    ⟨s,hu,hp⟩ whole).trans (bare E u s)

end LiteralKayles.PairedGraph
#print axioms LiteralKayles.PairedGraph.pendant_p4_pair

/-! A single two-vertex arm at an attachment vertex with a pendant leaf
has precisely the effect of a detached isolated vertex. -/
namespace LiteralKayles.PairedGraph
open Vertex

variable {V : Type} [DecidableEq V]

def two : Finset Q := {0,1}
def isolate : Finset Q := {3}

private theorem two_value : value path two = 1 := by decide
private theorem isolate_value : value path isolate = 1 := by decide
private theorem two_trim : value path (two.erase 0) = 1 := by decide
private theorem iso_trim : value path (isolate.erase 0) = 1 := by decide
private theorem two_root : drop path two 0 = ∅ := by decide
private theorem two_tip : drop path two 1 = ∅ := by decide
private theorem iso_move : drop path isolate 3 = ∅ := by decide

theorem isolate_board (E : V → V → Bool) (u : V) (s : Finset V) :
    value (adj E u) (board s isolate ∅) = value E s ^^^ 1 := by
  have sep : Separated (adj E u) (s.map hEmb) (isolate.map lEmb) := by
    rintro x hx y hy
    obtain ⟨v,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hy
    have ei : i=3 := Finset.mem_singleton.mp hi
    subst i
    simp [adj]
  simp only [board,Finset.map_empty,Finset.union_empty]
  rw [value_union _ _ _ sep,value_map E (adj E u) hEmb (fun _ _ => rfl),
    value_map path (adj E u) lEmb (fun _ _ => rfl),isolate_value]

private theorem equal_options (E : V → V → Bool) (s t : Finset V)
    (lr : ∀ x∈s, ∃ y∈t, value E (drop E t y) = value E (drop E s x))
    (rl : ∀ y∈t, ∃ x∈s, value E (drop E s x) = value E (drop E t y)) :
    value E s = value E t := by
  apply mex_unique (value_spec E s)
  obtain ⟨avoid,full⟩ := value_spec E t
  constructor
  · rintro ⟨x,hx,e⟩
    obtain ⟨y,hy,ey⟩ := lr x hx
    exact avoid ⟨y,hy,ey.trans e⟩
  · intro k hk
    obtain ⟨y,hy,e⟩ := full k hk
    obtain ⟨x,hx,ex⟩ := rl y hy
    exact ⟨x,hx,ex.trans e⟩

theorem two_matches_isolate (E : V → V → Bool) {u p : V} (leaf : LeafAt E u p)
    (s : Finset V) (hu : u∈s) (hp : p∈s) :
    value (adj E u) (board s two ∅) = value (adj E u) (board s isolate ∅) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    have atHost (v : V) (hv : v∈s) :
        value (adj E u) (drop (adj E u) (board s two ∅) (host v)) =
        value (adj E u) (drop (adj E u) (board s isolate ∅) (host v)) := by
      by_cases keep : u∈drop E s v
      · rw [host_quiet_value E _ _ keep,host_quiet_value E _ _ keep]
        have lt : drop E s v ⊂ s := Finset.ssubset_iff_subset_ne.mpr
          ⟨drop_sub ..,fun e => (drop_lt E s hv).ne (congrArg Finset.card e)⟩
        exact ih _ lt keep (keep_leaf E leaf hp keep)
      · rw [drop_host,drop_host,detached _ _ _ _ _ keep,detached _ _ _ _ _ keep]
        by_cases h : v=u <;> simp [h,two_value,isolate_value,two_trim,iso_trim]
    have atTip :
        value (adj E u) (drop (adj E u) (board s two ∅) (left 1)) =
        value (adj E u) (drop (adj E u) (board s isolate ∅) (left 3)) := by
      rw [drop_left,drop_left,two_tip,iso_move]; rfl
    have atRoot :
        value (adj E u) (drop (adj E u) (board s two ∅) (left 0)) =
        value (adj E u) (drop (adj E u) (board s isolate ∅) (host p)) := by
      rw [drop_left,ite_eq_left rfl,two_root,bare,drop_host,ite_eq_right leaf.1,
        ite_eq_right leaf.1,isolate_board,leaf_option E leaf hp]
      simp
    apply equal_options
    · intro x hx
      cases x with
      | host v => exact ⟨host v,by simpa using hx,(atHost v (by simpa using hx)).symm⟩
      | left i =>
        have hi : i=0 ∨ i=1 := by simpa [two] using hx
        rcases hi with rfl|rfl
        · exact ⟨host p,by simpa using hp,atRoot.symm⟩
        · exact ⟨left 3,by simp [isolate],atTip.symm⟩
      | right i => simp at hx
    · intro y hy
      cases y with
      | host v => exact ⟨host v,by simpa using hy,atHost v (by simpa using hy)⟩
      | left i =>
        have hi : i=3 := by simpa [isolate] using hy
        subst i
        exact ⟨left 1,by simp [two],atTip⟩
      | right i => simp at hy

/-- Adding an endpoint-rooted P2 flips the low bit for any finite host
with a pendant leaf at its attachment vertex. -/
theorem pendant_p2_shift (E : V → V → Bool) {u p : V} (leaf : LeafAt E u p)
    (s : Finset V) (hu : u∈s) (hp : p∈s) :
    value (adj E u) (board s two ∅) = value E s ^^^ 1 :=
  (two_matches_isolate E leaf s hu hp).trans (isolate_board E u s)

end LiteralKayles.PairedGraph
#print axioms LiteralKayles.PairedGraph.pendant_p2_shift
