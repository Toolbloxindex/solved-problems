module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

open scoped BigOperators

namespace UnicyclicClosure

structure Rooted (V : Type) where
  graph : SimpleGraph V
  root : V

namespace Rooted

variable {V W : Type}

def node : Rooted Unit := ⟨⊥, ()⟩

def attach (G : Rooted V) (H : Rooted W) : Rooted (V ⊕ W) :=
  ⟨G.graph.sum H.graph ⊔ SimpleGraph.edge (.inl G.root) (.inr H.root), .inl G.root⟩

def addEdge (G : Rooted V) (u v : V) : Rooted V :=
  ⟨G.graph ⊔ SimpleGraph.edge u v, G.root⟩

instance (v w : V) [DecidableEq V] : DecidableRel (SimpleGraph.edge v w).Adj :=
  fun x y => decidable_of_iff _ (SimpleGraph.edge_adj v w x y).symm

instance : DecidableRel node.graph.Adj := fun _ _ => inferInstanceAs (Decidable False)

instance (G : Rooted V) (H : Rooted W) [DecidableEq V] [DecidableEq W]
    [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj] :
    DecidableRel (G.attach H).graph.Adj := by
  letI : DecidableRel (G.graph.sum H.graph).Adj := fun a b => by
    cases a with
    | inl u =>
      cases b with
      | inl v => exact inferInstanceAs (Decidable (G.graph.Adj u v))
      | inr v => exact decidable_of_iff False (by simp)
    | inr u =>
      cases b with
      | inl v => exact decidable_of_iff False (by simp)
      | inr v => exact inferInstanceAs (Decidable (H.graph.Adj u v))
  change DecidableRel
    (G.graph.sum H.graph ⊔ SimpleGraph.edge (.inl G.root) (.inr H.root)).Adj
  infer_instance

instance (G : Rooted V) (u v : V) [DecidableEq V] [DecidableRel G.graph.Adj] :
    DecidableRel (G.addEdge u v).graph.Adj := by
  change DecidableRel (G.graph ⊔ SimpleGraph.edge u v).Adj
  infer_instance

end Rooted

inductive Build
  | node
  | attach (left right : Build)
  | markedArms
  deriving Inhabited

namespace Build

def arm : Rooted (Unit ⊕ Unit) := Rooted.node.attach Rooted.node

def twoArms : Rooted ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ Unit)) :=
  (Rooted.node.attach arm).attach arm

def firstMiddle : (Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ Unit) := .inl (.inr (.inl ()))

def secondMiddle : (Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ Unit) := .inr (.inl ())

def marked (close : Bool) : Rooted ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ Unit)) :=
  if close then twoArms.addEdge firstMiddle secondMiddle else twoArms

def V : Build → Type
  | .node => Unit
  | .attach A B => A.V ⊕ B.V
  | .markedArms => (Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ Unit)

instance fintypeV : (B : Build) → Fintype B.V
  | .node => inferInstanceAs (Fintype Unit)
  | .attach L R => by
    letI := fintypeV L
    letI := fintypeV R
    exact inferInstanceAs (Fintype (L.V ⊕ R.V))
  | .markedArms => inferInstanceAs (Fintype ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ Unit)))

instance decEqV : (B : Build) → DecidableEq B.V
  | .node => inferInstanceAs (DecidableEq Unit)
  | .attach L R => by
    letI := decEqV L
    letI := decEqV R
    exact inferInstanceAs (DecidableEq (L.V ⊕ R.V))
  | .markedArms => inferInstanceAs (DecidableEq ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ Unit)))

def rooted (close : Bool) : (B : Build) → Rooted B.V
  | .node => Rooted.node
  | .attach L R => (L.rooted close).attach (R.rooted close)
  | .markedArms => marked close

instance : DecidableRel arm.graph.Adj := by
  unfold arm
  infer_instance

instance : DecidableRel twoArms.graph.Adj := by
  unfold twoArms
  infer_instance

instance markedDecAdj (close : Bool) : DecidableRel (marked close).graph.Adj := by
  cases close
  · exact inferInstanceAs (DecidableRel twoArms.graph.Adj)
  · exact inferInstanceAs (DecidableRel (twoArms.addEdge firstMiddle secondMiddle).graph.Adj)

instance rootedDecAdj (close : Bool) : (B : Build) → DecidableRel (B.rooted close).graph.Adj
  | .node => inferInstanceAs (DecidableRel Rooted.node.graph.Adj)
  | .attach L R => by
    letI := rootedDecAdj close L
    letI := rootedDecAdj close R
    exact inferInstanceAs (DecidableRel ((L.rooted close).attach (R.rooted close)).graph.Adj)
  | .markedArms => markedDecAdj close

def marks : Build → ℕ
  | .node => 0
  | .attach L R => L.marks + R.marks
  | .markedArms => 1

def repeatAttach (A B : Build) : ℕ → Build
  | 0 => A
  | n + 1 => (repeatAttach A B n).attach B

def spider (n : ℕ) : Build := repeatAttach .node (.attach .node .node) n

def pattern (ell extraArms extraSpiders extraHubs : ℕ) : Build :=
  let star := spider (extraArms + 2)
  let branch := repeatAttach .node star (extraSpiders + 1)
  let markedStar := repeatAttach .markedArms (.attach .node .node) extraArms
  let markedBranch := repeatAttach (.attach .node markedStar) star extraSpiders
  repeatAttach ((node.attach (spider ell)).attach markedBranch) branch extraHubs

def TG25 : Build := pattern 0 3 2 1

def patternTwo16 : Build := pattern 3 2 1 15

def patternThree13 : Build := pattern 7 3 1 12

end Build

namespace Rooted
variable {V : Type} [Fintype V] [DecidableEq V] (G : Rooted V) [DecidableRel G.graph.Adj]

def count (k : ℕ) : ℕ := (G.graph.indepSetFinset k).card

end Rooted

def Unimodal (c : ℕ → ℕ) : Prop :=
  ∃ p, (∀ k < p, c k ≤ c (k + 1)) ∧ (∀ k, p ≤ k → c (k + 1) ≤ c k)

def BreakAt (c : ℕ → ℕ) (k : ℕ) : Prop :=
  0 < k ∧ c k ^ 2 < c (k - 1) * c (k + 1)

namespace Build
def GoodClosure (B : Build) (indices : List ℕ) : Prop :=
  (B.rooted false).graph.IsTree ∧
    (∃ u v : B.V, u ≠ v ∧ ¬(B.rooted false).graph.Adj u v ∧
      (B.rooted true).graph = (B.rooted false).graph ⊔ SimpleGraph.edge u v) ∧
    Unimodal (B.rooted true).count ∧
    ∀ k ∈ indices, BreakAt (B.rooted true).count k

end Build

open Build in
theorem problem_6_6 :
    TG25.GoodClosure [34, 36] ∧
    patternTwo16.GoodClosure [162, 163] ∧
    patternThree13.GoodClosure [161, 162, 163] := by sorry

end UnicyclicClosure
