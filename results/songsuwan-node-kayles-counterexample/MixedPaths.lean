import RayMoves
import LeafIdentities
import BoardMap
import Mathlib.Data.Finset.Fold

namespace KaylesRays.MixedPaths
open LiteralKayles Sum

abbrev Site (V : Type) := V ⊕ (Nat × Fin 5)
abbrev Arms := Nat → Finset (Fin 5)
abbrev path := FiveMoves.rayEdge

variable {V : Type} [DecidableEq V]

def siteEdge (E : V → V → Bool) (u : V) : Site V → Site V → Bool
  | inl v, inl w => E v w
  | inl v, inr (_,i) | inr (_,i), inl v => decide (v=u ∧ i=0)
  | inr (n,i), inr (m,j) => decide (n=m) && path i j

def pathPrefix (length : Nat) : Finset (Fin 5) :=
  Finset.univ.filter fun i => i.val < length

@[simp] theorem mem_pathPrefix (i : Fin 5) (length : Nat) :
    i ∈ pathPrefix length ↔ i.val < length := by simp [pathPrefix]

def block (n : Nat) (a : Finset (Fin 5)) : Finset (Site V) :=
  a.image (fun i => inr (n,i))

def mixed (s : Finset V) (ids : Finset Nat) (f : Arms) : Finset (Site V) :=
  s.map Function.Embedding.inl ∪ ids.biUnion (fun n => block n (f n))

@[simp] theorem mem_old (s : Finset V) (ids : Finset Nat) (f : Arms) (v : V) :
    inl v ∈ mixed s ids f ↔ v ∈ s := by simp [mixed,block,Finset.mem_map]

@[simp] theorem mem_ray (s : Finset V) (ids : Finset Nat) (f : Arms) (n : Nat) (i : Fin 5) :
    inr (n,i) ∈ mixed s ids f ↔ n∈ids ∧ i∈f n := by
  simp [mixed,block,Finset.mem_map]

def replace (f : Arms) (n : Nat) (a : Finset (Fin 5)) : Arms :=
  fun m => if m=n then a else f m

def score (E : V → V → Bool) (u : V) (s : Finset V) (ids : Finset Nat) (f : Arms) :=
  value (siteEdge E u) (mixed s ids f)

def after (E : V → V → Bool) (u : V) (s : Finset V) (ids : Finset Nat) (f : Arms) (a : Site V) :=
  value (siteEdge E u) (drop (siteEdge E u) (mixed s ids f) a)

theorem host_drop (E : V → V → Bool) (u v : V) (s : Finset V) (ids : Finset Nat) (f : Arms) :
    drop (siteEdge E u) (mixed s ids f) (inl v) =
      mixed (drop E s v) ids (fun n => if v=u then (f n).erase 0 else f n) := by
  ext x
  rcases x with (w|⟨n,i⟩)
  · simp [drop,siteEdge]
  · by_cases e : v=u <;> simp [drop,siteEdge,e,and_assoc,and_comm]

theorem arm_drop (E : V → V → Bool) (u : V) (s : Finset V) (ids : Finset Nat)
    (f : Arms) (n : Nat) (i : Fin 5) :
    drop (siteEdge E u) (mixed s ids f) (inr (n,i)) =
      mixed (if i=0 then s.erase u else s) ids (replace f n (drop path (f n) i)) := by
  ext x
  rcases x with (v|⟨m,j⟩)
  · by_cases e : i=0 <;> simp [drop,siteEdge,e,and_comm]
  · by_cases e : m=n
    · subst m
      simp [drop,siteEdge,replace,and_assoc]
    · simp [drop,siteEdge,replace,e,Ne.symm e]

theorem arm_insert (s : Finset V) (ids : Finset Nat) (f : Arms) {n : Nat} (hn : n∉ids)
    (a : Finset (Fin 5)) :
    mixed s (insert n ids) (replace f n a) = mixed s ids f ∪ block n a := by
  ext x
  rcases x with (v|⟨m,i⟩)
  · simp [block]
  · by_cases e : m=n
    · subst m; simp [block,replace,hn]
    · simp [block,replace,e,Ne.symm e]

private theorem block_value (E : V → V → Bool) (u : V) (n : Nat) (a : Finset (Fin 5)) :
    value (siteEdge E u) (block n a) = value path a := by
  unfold block
  exact value_image path (siteEdge E u) (fun i => inr (n,i)) a
    (fun _ _ _ _ h => (Prod.mk.inj (Sum.inr.inj h)).2)
    (fun i _ j _ => by simp [siteEdge])

theorem detached_insert (E : V → V → Bool) (u : V) (s : Finset V) (ids : Finset Nat)
    (f : Arms) {n : Nat} (hn : n∉ids) (a : Finset (Fin 5)) (cut : u∉s ∨ 0∉a) :
    score E u s (insert n ids) (replace f n a) = score E u s ids f ^^^ value path a := by
  have sep : Separated (siteEdge E u) (mixed s ids f) (block n a) := by
    intro x hx y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    rcases x with (v|⟨m,j⟩)
    · have h : ¬(v=u ∧ i=0) := by
        rintro ⟨rfl,rfl⟩
        exact cut.elim (fun h => h (mem_old .. |>.mp hx)) (fun h => h hi)
      simp [siteEdge,h]
    · have h : m≠n := by
        rintro rfl
        exact hn ((mem_ray .. |>.mp hx).1)
      simp [siteEdge,h,Ne.symm h]
  unfold score
  rw [arm_insert s ids f hn,value_union _ _ _ sep,block_value]

local instance : Std.Commutative Nat.xor := ⟨Nat.xor_comm⟩
local instance : Std.Associative Nat.xor := ⟨Nat.xor_assoc⟩

theorem detached (E : V → V → Bool) (u : V) (s : Finset V) (ids : Finset Nat)
    (f : Arms) (hu : u∉s) :
    score E u s ids f = value E s ^^^ ids.fold Nat.xor 0 (fun n => value path (f n)) := by
  induction ids using Finset.induction_on with
  | empty =>
    simp only [score,mixed,Finset.biUnion_empty,Finset.union_empty,Finset.fold_empty,Nat.xor_zero]
    exact value_map E _ _ (fun _ _ => rfl) s
  | @insert n ids hn ih =>
    have replace_eq : replace f n (f n) = f := by
      funext m
      by_cases e : m=n <;> simp [replace,e]
    conv_lhs => rw [← replace_eq]
    rw [detached_insert E u s ids f hn (f n) (Or.inl hu),ih, Finset.fold_insert hn]
    rw [Nat.xor_assoc, Nat.xor_comm (ids.fold Nat.xor 0 (fun n => value path (f n))) (value path (f n))]
    rfl

private def rooted (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (f : Arms) : Erasure.Rooted where
  V := Site V
  eqV := inferInstance
  E := siteEdge E u
  u := inl u
  board := mixed s ids f
  live := by simp [hu]

private theorem rooted_score (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (f : Arms) :
    FiveMoves.score (rooted E u s hu ids f) = score E u s ids f := rfl

private def graft (n : Nat) : Site V ⊕ Fin 5 → Site V
  | inl v => v
  | inr i => inr (n,i)

private theorem graft_board (s : Finset V) (ids : Finset Nat) (f : Arms) (n : Nat) (a : Finset (Fin 5)) :
    ((mixed s ids f).disjSum a).image (graft n) = mixed s ids f ∪ block n a := by
  ext v
  constructor
  · rintro hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    cases x with
    | inl x => exact Finset.mem_union_left _ (Finset.inl_mem_disjSum.mp hx)
    | inr i => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.inr_mem_disjSum.mp hx,rfl⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hx|hx
    · exact Finset.mem_image.mpr ⟨inl v,Finset.inl_mem_disjSum.mpr hx,rfl⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨inr i,Finset.inr_mem_disjSum.mpr hi,rfl⟩

private theorem graft_inj (s : Finset V) (ids : Finset Nat) (f : Arms)
    {n : Nat} (hn : n∉ids) (a : Finset (Fin 5)) :
    Set.InjOn (graft n) (↑((mixed s ids f).disjSum a) : Set (Site V ⊕ Fin 5)) := by
  intro x hx y hy e
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg inl e
    | inr j =>
      change x=inr (n,j) at e
      subst x
      exact (hn ((mem_ray .. |>.mp (Finset.inl_mem_disjSum.mp hx)).1)).elim
  | inr i =>
    cases y with
    | inl y =>
      change inr (n,i)=y at e
      subst y
      exact (hn ((mem_ray .. |>.mp (Finset.inl_mem_disjSum.mp hy)).1)).elim
    | inr j => simpa [graft] using e

private theorem graft_edges (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (f : Arms) {n : Nat} (hn : n∉ids) (length : Nat) (hl : 0<length)
    (v w : Site V ⊕ Fin 5)
    (hv : v∈(mixed s ids f).disjSum (pathPrefix length))
    (hw : w∈(mixed s ids f).disjSum (pathPrefix length)) :
    siteEdge E u (graft n v) (graft n w) =
      Erasure.joined (rooted E u s hu ids f) (FiveMoves.arm length hl) v w := by
  rcases v with (v|i) <;> rcases w with (w|j)
  · rfl
  · rcases v with (v|⟨m,i⟩)
    · simp [graft,siteEdge,Erasure.joined,rooted,FiveMoves.arm]
    · have ne : m≠n := fun h => hn (h ▸ (mem_ray .. |>.mp (Finset.inl_mem_disjSum.mp hv)).1)
      simp [graft,siteEdge,Erasure.joined,rooted,ne]
  · rcases w with (w|⟨m,j⟩)
    · simp [graft,siteEdge,Erasure.joined,rooted,FiveMoves.arm]
    · have ne : n≠m := fun h => hn (h.symm ▸ (mem_ray .. |>.mp (Finset.inl_mem_disjSum.mp hw)).1)
      simp [graft,siteEdge,Erasure.joined,rooted,ne]
  · simp [graft,siteEdge,Erasure.joined]

private theorem graft_score (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (f : Arms) {n : Nat} (hn : n∉ids) (length : Nat) (hl : 0<length) :
    FiveMoves.score (Erasure.attach (rooted E u s hu ids f) (FiveMoves.arm length hl)) =
      score E u s (insert n ids) (replace f n (pathPrefix length)) := by
  symm
  unfold FiveMoves.score score
  change value (siteEdge E u) (mixed s (insert n ids) (replace f n (pathPrefix length))) =
    value (Erasure.joined (rooted E u s hu ids f) (FiveMoves.arm length hl))
      ((mixed s ids f).disjSum (pathPrefix length))
  rw [arm_insert s ids f hn,← graft_board]
  exact value_image _ _ (graft n) _ (graft_inj s ids f hn _)
    (fun v hv w hw => graft_edges E u s hu ids f hn length hl v w hv hw)

private theorem graft_after (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (f : Arms) {n : Nat} (hn : n∉ids) (length : Nat) (hl : 0<length)
    (i : Fin 5) (hi : i∈pathPrefix length) :
    after E u s (insert n ids) (replace f n (pathPrefix length)) (inr (n,i)) =
      FiveMoves.after (rooted E u s hu ids f) (FiveMoves.arm length hl) i := by
  let B := (mixed s ids f).disjSum (pathPrefix length)
  let A : (Site V ⊕ Fin 5) → (Site V ⊕ Fin 5) → Bool := Erasure.joined (rooted E u s hu ids f) (FiveMoves.arm length hl)
  have inj := graft_inj s ids f hn (pathPrefix length)
  have pres := fun v (hv : v∈B) w (hw : w∈B) =>
    graft_edges E u s hu ids f hn length hl v w hv hw
  have hi' : (inr i : Site V ⊕ Fin 5) ∈ B := Finset.inr_mem_disjSum.mpr hi
  have eq : drop (siteEdge E u) (B.image (graft n)) (inr (n,i)) =
      (drop A B (inr i)).image (graft n) := by
    ext v
    constructor
    · intro hv
      obtain ⟨mem,ne,edge⟩ := Finset.mem_filter.mp hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp mem
      exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr
        ⟨hw,fun e => ne (congrArg (graft n) e), (pres _ hi' _ hw).symm.trans edge⟩,rfl⟩
    · intro hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hw,ne,edge⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,
        fun e => ne (inj hw hi' e), (pres _ hi' _ hw).trans edge⟩
  unfold after
  rw [arm_insert s ids f hn,← graft_board,eq]
  exact value_image _ _ _ _ (fun _ hv _ hw => inj (drop_sub _ _ _ hv) (drop_sub _ _ _ hw))
    (fun v hv w hw => pres v (drop_sub _ _ _ hv) w (drop_sub _ _ _ hw))

/-- Five-branch interior moves, carried from the one-branch literal path
calculation to an arbitrary inventory. -/
theorem five (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (f : Arms) {n : Nat} (hn : n∉ids) :
    let play := fun i => after E u s (insert n ids) (replace f n (pathPrefix 5)) (inr (n,i))
    let put := fun l => score E u s (insert n ids) (replace f n (pathPrefix l))
    play 1 = score E u s ids f ^^^ 1 ∧
    play 2 = put 1 ^^^ 1 ∧ play 3 = put 2 ∧ play 4 = put 3 := by
  dsimp only
  rw [graft_after E u s hu ids f hn 5 (by decide) 1 (by decide),
    graft_after E u s hu ids f hn 5 (by decide) 2 (by decide),
    graft_after E u s hu ids f hn 5 (by decide) 3 (by decide),
    graft_after E u s hu ids f hn 5 (by decide) 4 (by decide)]
  simpa only [graft_score E u s hu ids f hn 1 (by decide),
    graft_score E u s hu ids f hn 2 (by decide),graft_score E u s hu ids f hn 3 (by decide),
    rooted_score] using
      FiveMoves.five (rooted E u s hu ids f)

theorem three (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (f : Arms) {n : Nat} (hn : n∉ids) :
    let play := fun i => after E u s (insert n ids) (replace f n (pathPrefix 3)) (inr (n,i))
    play 1 = score E u s ids f ∧
    play 2 = score E u s (insert n ids) (replace f n (pathPrefix 1)) := by
  dsimp only
  rw [graft_after E u s hu ids f hn 3 (by decide) 1 (by decide),
    graft_after E u s hu ids f hn 3 (by decide) 2 (by decide)]
  simpa only [graft_score E u s hu ids f hn 1 (by decide),rooted_score] using
    FiveMoves.three (rooted E u s hu ids f)

end KaylesRays.MixedPaths
