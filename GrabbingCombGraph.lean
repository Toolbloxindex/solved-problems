module

public import GrabbingGraph
public import GrabbingComb

@[expose] public section

namespace GraphGrabbing.Comb
open Finset

/-- Even labels are hubs. Their pendant leaves have the next odd label. -/
def encode : Token → ℕ
  | .hub i => 2*i
  | .leaf i => 2*i+1

def edges (x y : ℕ) : Prop :=
  (x%2=0 ∧ (y=x+1 ∨ y=x+2)) ∨ (y%2=0 ∧ (x=y+1 ∨ x=y+2))

def board (h : ℕ) (L : Finset ℕ) : Vertices :=
  (range h).image (fun i => 2*i) ∪ L.image (fun i => 2*i+1)

private theorem symmetric : Undirected edges := by
  intro x y e
  exact e.elim Or.inr Or.inl

@[simp] theorem mem_hub {h L i} : 2*i∈board h L ↔ i<h := by
  simp only [board,mem_union,mem_image,mem_range]
  constructor
  · rintro (⟨j,hj,eq⟩|⟨j,hj,eq⟩) <;> omega
  · exact fun hi => Or.inl ⟨i,hi,rfl⟩

@[simp] theorem mem_leaf {h L i} : 2*i+1∈board h L ↔ i∈L := by
  simp only [board,mem_union,mem_image,mem_range]
  constructor
  · rintro (⟨j,hj,eq⟩|⟨j,hj,eq⟩)
    · omega
    · exact (by omega : j=i) ▸ hj
  · exact fun hi => Or.inr ⟨i,hi,rfl⟩

private theorem empty_connected : Connected edges ∅ := by
  intro A sub ha
  obtain ⟨x,hx⟩ := ha
  exact (notMem_empty x (sub hx)).elim

private theorem bare_connected (h : ℕ) : Connected edges (board h ∅) := by
  induction h with
  | zero => simpa [board] using empty_connected
  | succ h ih =>
    have eq : board (h+1) ∅=insert (2*h) (board h ∅) := by simp [board,range_add_one]
    rw [eq]
    cases h with
    | zero => simpa [board] using singleton_connected edges 0
    | succ k =>
      apply insert_connected symmetric ih (mem_hub.mpr (Nat.lt_succ_self k))
      unfold edges
      omega

theorem board_connected {h L} (fit : Fits h L) : Connected edges (board h L) := by
  induction L using Finset.induction_on with
  | empty => exact bare_connected _
  | insert i L hi ih =>
    have eq : board h (insert i L)=insert (2*i+1) (board h L) := by
      simp [board,union_insert]
    rw [eq]
    apply insert_connected symmetric (ih (fun j hj => fit j (mem_insert_of_mem hj)))
      (mem_hub.mpr (fit i (mem_insert_self ..)))
    unfold edges
    omega

theorem board_erase {h L x k M} (m : Move h L x k M) :
    (board h L).erase (encode x)=board k M := by
  ext z
  have halves : z=2*(z/2) ∨ z=2*(z/2)+1 := by omega
  rcases halves with e|e
  · generalize z/2=i at e
    subst z
    cases m with
    | hub => simp only [encode,mem_erase,mem_hub]; omega
    | leaf => simp only [encode,mem_erase,mem_hub]; omega
  · generalize z/2=i at e
    subst z
    cases m with
    | hub free => simp [encode,show 2*i+1≠2*k by omega]
    | @leaf h L j mem =>
      simp only [encode,mem_erase,mem_leaf]
      rw [show (2*i+1≠2*j+1) ↔ i≠j by omega]

/-- Connected remainder and singleton root retained right up to the last move. -/
def RootLegal (S : Vertices) (z : ℕ) :=
  Legal edges S z ∧ (S.erase z=∅ ∨ 0∈S.erase z)

private theorem retains_root {h L} (fit : Fits h L) : board h L=∅ ∨ 0∈board h L := by
  cases h with
  | zero =>
    left
    have eq : L=∅ := eq_empty_iff_forall_notMem.mpr (fun i hi => by have := fit i hi; omega)
    simp [board,eq]
  | succ k => exact Or.inr (mem_hub.mpr (Nat.zero_lt_succ k) : 2*0∈_)

theorem legal_of_move {h L x k M} (fit : Fits h L) (m : Move h L x k M) :
    RootLegal (board h L) (encode x) := by
  have wf := move_fits m fit
  refine ⟨⟨?_,(board_erase m) ▸ board_connected wf⟩,(board_erase m) ▸ retains_root wf⟩
  cases m with
  | hub => exact mem_hub.mpr (Nat.lt_succ_self _)
  | leaf mem => exact mem_leaf.mpr mem

private theorem legal_hub {h L i} (legal : RootLegal (board h L) (2*i)) :
    h=i+1 ∧ i∉L := by
  obtain ⟨⟨mem,conn⟩,root⟩ := legal
  have hi := mem_hub.mp mem
  let S := (board h L).erase (2*i)
  have zero (ne : S.Nonempty) : 0∈S := root.resolve_left ne.ne_empty
  have endHub : h=i+1 := by
    by_contra no
    have next : 2*(i+1)∈S := mem_erase.mpr ⟨by omega,mem_hub.mpr (by omega)⟩
    have keep := zero ⟨_,next⟩
    have nz := (mem_erase.mp keep).1
    let A := S.filter fun x => x<2*i
    have ha : 0∈A := mem_filter.mpr ⟨keep,by omega⟩
    have hb : 2*(i+1)∈S \ A := mem_sdiff.mpr ⟨next,fun e => by
      have lt := (mem_filter.mp e).2
      omega⟩
    obtain ⟨u,hu,v,hv,uv⟩ := conn A (filter_subset ..) ⟨_,ha⟩ ⟨_,hb⟩
    obtain ⟨vu,notA⟩ := mem_sdiff.mp hv
    have left := (mem_filter.mp hu).2
    have right : ¬v<2*i := fun lt => notA (mem_filter.mpr ⟨vu,lt⟩)
    have excluded := (mem_erase.mp vu).1
    unfold edges at uv
    omega
  refine ⟨endHub,?_⟩
  intro leaf
  have stay : 2*i+1∈S := mem_erase.mpr ⟨by omega,mem_leaf.mpr leaf⟩
  obtain ⟨z,hz,_,edge⟩ := neighbor conn stay (zero ⟨_,stay⟩) (by omega)
  have ne := (mem_erase.mp hz).1
  unfold edges at edge
  omega

/-- Exact source-to-state mapping of every legal rooted deletion, including
the empty remainder. -/
theorem rootLegal_iff {h L} (fit : Fits h L) (x : Token) :
    RootLegal (board h L) (encode x) ↔ x∈choices h L := by
  constructor
  · intro legal
    cases x with
    | leaf i => exact (move_choice (Move.leaf (h:=h) (mem_leaf.mp legal.1.1))).1
    | hub i =>
      obtain ⟨rfl,free⟩ := legal_hub legal
      exact (move_choice (Move.hub free)).1
  · exact fun hx => legal_of_move fit (choice_move hx)

def decode (z : ℕ) : Token := if z%2=0 then .hub (z/2) else .leaf (z/2)

private theorem encode_decode (z : ℕ) : encode (decode z)=z := by
  unfold decode
  split <;> simp only [encode] <;> omega

def weight (u w : ℕ → ℝ) (z : ℕ) : ℝ := if z%2=0 then u (z/2) else w (z/2)

private theorem weight_encode (u w : ℕ → ℝ) (x : Token) : weight u w (encode x)=loot u w x := by
  cases x with
  | hub i => simp [encode,weight,loot]
  | leaf i => simp [encode,weight,loot,show (2*i+1)/2=i by omega]

noncomputable def rootMoves (S : Vertices) : Vertices := by
  classical exact S.filter (RootLegal S)

private theorem mem_rootMoves {S z} : z∈rootMoves S ↔ RootLegal S z := by
  classical
  simp only [rootMoves,mem_filter]
  exact ⟨And.right,fun h => ⟨h.1.1,h⟩⟩

/-- Literal connectivity-preserving negamax with hub zero held to the last move. -/
noncomputable def rootedValue (w : ℕ → ℝ) : ℕ → Vertices → ℝ
  | 0, _ => 0
  | f+1, S => if ne : (rootMoves S).Nonempty then
      (rootMoves S).sup' ne fun z => w z-rootedValue w f (S.erase z)
    else 0

private theorem eval_eq (u w : ℕ → ℝ) (fuel : ℕ) {h L} (fit : Fits h L)
    (size : h+L.card=fuel) : rootedValue (weight u w) fuel (board h L) =
      2*score u w fuel h L-mass u w h L := by
  induction fuel generalizing h L with
  | zero =>
    have hz : h=0 := by omega
    have lz : L=∅ := card_eq_zero.mp (by omega)
    subst h; subst L
    simp [rootedValue,score,mass]
  | succ f ih =>
    have ne : (choices h L).Nonempty := by
      rcases L.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
      · have hp : 0<h := by simp_all
        exact ⟨Token.hub (h-1),by simp [choices,hp]⟩
      · exact ⟨_,(move_choice (Move.leaf (h:=h) hi)).1⟩
    obtain ⟨a,ha⟩ := ne
    have rg : (rootMoves (board h L)).Nonempty :=
      ⟨_,mem_rootMoves.mpr ((rootLegal_iff fit a).mpr ha)⟩
    have transfer {x k M} (m : Move h L x k M) :
        weight u w (encode x)-rootedValue (weight u w) f ((board h L).erase (encode x)) =
        2*(mass u w h L-score u w f k M)-mass u w h L := by
      have sz := move_size m
      rw [board_erase m,ih (move_fits m fit) (by omega),weight_encode]
      have total : mass u w h L=loot u w x+mass u w k M := by
        cases m with
        | hub => simp [mass,sum_range_succ,loot,add_left_comm,add_comm]
        | @leaf _ _ i mem =>
          simp only [mass,loot]
          linarith only [sum_erase_add _ w mem]
      linarith
    rw [rootedValue,dite_eq_left rg,score,dite_eq_left ⟨_,ha⟩]
    apply le_antisymm
    · apply sup'_le
      intro z hz
      let x := decode z
      have ex : encode x=z := encode_decode z
      have hx : x∈choices h L := (rootLegal_iff fit x).mp (ex ▸ mem_rootMoves.mp hz)
      have bound := (choices h L).le_sup' (f := fun y => mass u w h L-
        score u w f (nextH h y) (nextL L y)) hx
      rw [← ex,transfer (choice_move hx)]
      linarith only [bound]
    · obtain ⟨x,hx,eq⟩ := (choices h L).exists_mem_eq_sup' ⟨_,ha⟩
        (fun y => mass u w h L-score u w f (nextH h y) (nextL L y))
      have legal := mem_rootMoves.mpr ((rootLegal_iff fit x).mpr hx)
      have bound := (rootMoves (board h L)).le_sup' (f := fun z => weight u w z-
        rootedValue (weight u w) f ((board h L).erase z)) legal
      rw [eq,← transfer (choice_move hx)]
      exact bound

/-- Each rooted copy uses labels measured from its own root. Reversing the
labels on the second copy transports the same hubs, leaves and weights. -/
theorem opposite_rooted_values (u w : ℕ → ℝ) {n L} (fit : Fits n L)
    (even : n%2=0) (evenLeaves : L.card%2=0) (top : n-1∈L)
    (minimum : ∀ i∈L,w (n-1)≤w i) (nn : ∀ i∈L,0≤w i) :
    0 ≤ rootedValue (weight u w) (n+L.card) (board n L) +
        rootedValue (weight (u ∘ flip n) (w ∘ flip n)) (n+(L.image (flip n)).card)
          (board n (L.image (flip n))) := by
  have revFit : Fits n (L.image (flip n)) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    have := fit i hi
    unfold flip
    omega
  rw [eval_eq u w _ fit rfl,eval_eq _ _ _ revFit rfl]
  exact opposite_margins u w fit even evenLeaves top minimum nn

end GraphGrabbing.Comb
#print axioms GraphGrabbing.Comb.rootLegal_iff
#print axioms GraphGrabbing.Comb.opposite_rooted_values
