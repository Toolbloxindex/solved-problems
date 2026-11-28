module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

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

theorem indep_iff {G : SimpleGraph V} (s : Finset V) :
    G.IsIndepSet s ↔ ∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w := by
  refine ⟨fun h v hv w hw e => ?_, fun h _ hv _ hw _ => h _ hv _ hw⟩
  exact h hv hw e.ne e

theorem attach_indep_iff (G : Rooted V) (H : Rooted W) (s : Finset V) (t : Finset W) :
    (G.attach H).graph.IsIndepSet (s.disjSum t) ↔
      G.graph.IsIndepSet s ∧ H.graph.IsIndepSet t ∧ ¬(G.root ∈ s ∧ H.root ∈ t) := by
  simp only [indep_iff]
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun ⟨hg, hh, he⟩ => ?_⟩
  · intro a ha b hb e
    exact h (.inl a) (by simpa) (.inl b) (by simpa) (by simpa [attach, SimpleGraph.edge_adj])
  · intro a ha b hb e
    exact h (.inr a) (by simpa) (.inr b) (by simpa) (by simpa [attach, SimpleGraph.edge_adj])
  · rintro ⟨hs, ht⟩
    exact h (.inl G.root) (by simpa) (.inr H.root) (by simpa) (by simp [attach, SimpleGraph.edge_adj])
  · rintro (a | a) ha (b | b) hb e
    · exact hg a (by simpa using ha) b (by simpa using hb)
        (by simpa [attach, SimpleGraph.edge_adj] using e)
    · have e' : a = G.root ∧ b = H.root := by simpa [attach, SimpleGraph.edge_adj] using e
      exact he ⟨e'.1 ▸ (by simpa using ha : a ∈ s), e'.2 ▸ (by simpa using hb : b ∈ t)⟩
    · have e' : a = H.root ∧ b = G.root := by simpa [attach, SimpleGraph.edge_adj] using e
      exact he ⟨e'.2 ▸ (by simpa using hb : b ∈ s), e'.1 ▸ (by simpa using ha : a ∈ t)⟩
    · exact hh a (by simpa using ha) b (by simpa using hb)
        (by simpa [attach, SimpleGraph.edge_adj] using e)

theorem attach_root_mem (G : Rooted V) (H : Rooted W) (s : Finset V) (t : Finset W) :
    (G.attach H).root ∈ s.disjSum t ↔ G.root ∈ s := Finset.inl_mem_disjSum

def eval (G : Rooted V) [Fintype V] [DecidableEq V] [DecidableRel G.graph.Adj]
    (x : ℕ) (selected : Bool) : ℕ :=
  ∑ s : Finset V, if G.graph.IsIndepSet s ∧ (G.root ∈ s ↔ selected = true) then x ^ s.card else 0

theorem eval_attach (G : Rooted V) (H : Rooted W) [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj]
    (x : ℕ) (selected : Bool) :
    (G.attach H).eval x selected =
      G.eval x selected * (if selected then H.eval x false else H.eval x false + H.eval x true) := by
  unfold eval
  rw [← (Fintype.sum_equiv Finset.sumEquiv.symm.toEquiv _ _ (fun _ => rfl)), Fintype.sum_prod_type]
  split
  · rename_i hselected
    subst selected
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hs : G.root ∈ s <;> by_cases ht : H.root ∈ t <;>
      by_cases hg : G.graph.IsIndepSet s <;> by_cases hh : H.graph.IsIndepSet t <;>
      simp [attach_indep_iff, attach_root_mem, pow_add, hs, ht, hg, hh]
  · rename_i hselected
    have hf : selected = false := Bool.eq_false_of_not_eq_true hselected
    subst selected
    rw [Finset.sum_add_distrib.symm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hs : G.root ∈ s <;> by_cases ht : H.root ∈ t <;>
      by_cases hg : G.graph.IsIndepSet s <;> by_cases hh : H.graph.IsIndepSet t <;>
      simp [attach_indep_iff, attach_root_mem, pow_add, hs, ht, hg, hh]

end Rooted
end UnicyclicClosure
