module

public import GraphCount

@[expose] public section

set_option maxHeartbeats 50000

namespace UnicyclicClosure

namespace Rooted

variable {V W : Type}

theorem node_isTree : node.graph.IsTree := by
  refine ⟨⟨fun x y => ?_⟩, SimpleGraph.isAcyclic_bot⟩
  cases x; cases y
  exact SimpleGraph.Reachable.refl ()

theorem attach_isTree [Fintype V] [Fintype W] {G : Rooted V} {H : Rooted W}
    (hG : G.graph.IsTree) (hH : H.graph.IsTree) : (G.attach H).graph.IsTree := by
  refine SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hG.connected.sum_sup_edge hH.connected, ?_⟩
  have he := Nat.card_congr (SimpleGraph.edgeSetSumEquiv (G := G.graph) (H := H.graph))
  rw [Nat.card_sum] at he
  have hG' := hG.ncard_edgeSet_add_one
  have hH' := hH.ncard_edgeSet_add_one
  simp only [Nat.card_coe_set_eq] at he
  have hmiss : s(Sum.inl G.root, Sum.inr H.root) ∉ (G.graph.sum H.graph).edgeSet := by simp
  rw [Nat.card_coe_set_eq, Nat.card_sum]
  change (G.graph.sum H.graph ⊔ SimpleGraph.edge (.inl G.root) (.inr H.root)).edgeSet.ncard + 1 = _
  have hn : (Sum.inl G.root : V ⊕ W) ≠ Sum.inr H.root := by intro h; cases h
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hn, Set.union_singleton,
    Set.ncard_insert_of_notMem hmiss (Set.toFinite _), he]
  omega

@[simp] theorem attach_addEdge_left (G : Rooted V) (H : Rooted W) (u v : V) :
    (G.addEdge u v).attach H = (G.attach H).addEdge (.inl u) (.inl v) := by
  simp only [attach, addEdge, Rooted.mk.injEq, and_true]
  ext (a | a) (b | b) <;> simp [SimpleGraph.edge_adj]

@[simp] theorem attach_addEdge_right (G : Rooted V) (H : Rooted W) (u v : W) :
    G.attach (H.addEdge u v) = (G.attach H).addEdge (.inr u) (.inr v) := by
  simp only [attach, addEdge, Rooted.mk.injEq, and_true]
  ext (a | a) (b | b) <;> simp [SimpleGraph.edge_adj]

theorem attach_nonadj_left (G : Rooted V) (H : Rooted W) {u v : V} (h : ¬G.graph.Adj u v) :
    ¬(G.attach H).graph.Adj (.inl u) (.inl v) := by
  simpa [attach, SimpleGraph.edge_adj] using h

theorem attach_nonadj_right (G : Rooted V) (H : Rooted W) {u v : W} (h : ¬H.graph.Adj u v) :
    ¬(G.attach H).graph.Adj (.inr u) (.inr v) := by
  simpa [attach, SimpleGraph.edge_adj] using h

end Rooted

/-- Attach disjoint rooted graphs by joining their roots. The marked piece
consists of a root and two pendant two-edge paths, with an optional edge
between their middle vertices. -/
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

theorem rooted_eq_of_noMarks (B : Build) (h : B.marks = 0) : B.rooted true = B.rooted false := by
  induction B with
  | node => rfl
  | attach L R ihL ihR =>
    simp only [marks, Nat.add_eq_zero_iff] at h
    simp only [rooted, ihL h.1, ihR h.2]
    rfl
  | markedArms => simp [marks] at h

theorem isTree_unclosed (B : Build) : (B.rooted false).graph.IsTree := by
  induction B with
  | node => exact Rooted.node_isTree
  | attach L R hL hR =>
    change ((L.rooted false).attach (R.rooted false)).graph.IsTree
    exact Rooted.attach_isTree hL hR
  | markedArms =>
    change twoArms.graph.IsTree
    exact Rooted.attach_isTree
      (Rooted.attach_isTree Rooted.node_isTree (Rooted.attach_isTree Rooted.node_isTree Rooted.node_isTree))
      (Rooted.attach_isTree Rooted.node_isTree Rooted.node_isTree)

theorem closes_one_edge (B : Build) (h : B.marks = 1) :
    ∃ u v : B.V, u ≠ v ∧ ¬(B.rooted false).graph.Adj u v ∧
      B.rooted true = (B.rooted false).addEdge u v := by
  induction B with
  | node => simp [marks] at h
  | markedArms =>
    refine ⟨firstMiddle, secondMiddle, ?_, ?_, rfl⟩
    · intro he
      cases he
    · simp [rooted, marked, twoArms, Rooted.attach, firstMiddle, secondMiddle, SimpleGraph.edge_adj]
  | attach L R ihL ihR =>
    simp only [marks] at h
    have hs : (L.marks = 1 ∧ R.marks = 0) ∨ (L.marks = 0 ∧ R.marks = 1) := by omega
    rcases hs with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · obtain ⟨u,v, huv, hnot, he⟩ := ihL hl
      refine ⟨.inl u, .inl v, fun eq => huv (Sum.inl.inj eq), Rooted.attach_nonadj_left _ _ hnot, ?_⟩
      simp only [rooted, he, rooted_eq_of_noMarks _ hr, Rooted.attach_addEdge_left]
      rfl
    · obtain ⟨u,v, huv, hnot, he⟩ := ihR hr
      refine ⟨.inr u, .inr v, fun eq => huv (Sum.inr.inj eq), Rooted.attach_nonadj_right _ _ hnot, ?_⟩
      simp only [rooted, he, rooted_eq_of_noMarks _ hl, Rooted.attach_addEdge_right]
      rfl

def repeatAttach (A B : Build) : ℕ → Build
  | 0 => A
  | n + 1 => (repeatAttach A B n).attach B

/-- A rooted spider with `n` two-edge arms. -/
def spider (n : ℕ) : Build := repeatAttach .node (.attach .node .node) n

/-- The exceptional branch has `ell` two-edge arms. Each ordinary hub
has `extraSpiders + 1` spiders with `extraArms + 2` arms each, and the
central root has `extraHubs + 1` ordinary hubs. -/
def pattern (ell extraArms extraSpiders extraHubs : ℕ) : Build :=
  let star := spider (extraArms + 2)
  let branch := repeatAttach .node star (extraSpiders + 1)
  let markedStar := repeatAttach .markedArms (.attach .node .node) extraArms
  let markedBranch := repeatAttach (.attach .node markedStar) star extraSpiders
  repeatAttach ((node.attach (spider ell)).attach markedBranch) branch extraHubs

/-- Bautista–Ramos Definition 1(iv), Figure 1. -/
def TG25 : Build := pattern 0 3 2 1

/-- Bautista–Ramos, Guillén–Galván and Gómez–Salgado Corollary 4.13 at m=16. -/
def patternTwo16 : Build := pattern 3 2 1 15

/-- Bautista–Ramos, Guillén–Galván and Gómez–Salgado Corollary 4.14 at m=13. -/
def patternThree13 : Build := pattern 7 3 1 12

end Build

end UnicyclicClosure
