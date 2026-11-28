module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push

@[expose] public section

namespace GraphGrabbing
open Finset

abbrev Vertices := Finset ℕ

abbrev Edge := ℕ → ℕ → Prop

abbrev Undirected (E : Edge) := ∀ ⦃x y⦄, E x y → E y x

def Connected (E : Edge) (S : Vertices) : Prop :=
  ∀ A ⊆ S, A.Nonempty → (S \ A).Nonempty →
    ∃ u ∈ A, ∃ v ∈ S \ A, E u v

def Legal (E : Edge) (S : Vertices) (v : ℕ) := v ∈ S ∧ Connected E (S.erase v)

noncomputable def neighbors (E : Edge) (S : Vertices) (x : ℕ) : Vertices := by
  classical
  exact S.filter (E x)

def LongClaw (E : Edge) (S : Vertices) : Prop :=
  ∃ x∈S, ∃ N⊆neighbors E S x, 3≤N.card ∧
    ∀ y∈N, ∃ u∈S, u≠x ∧ E y u ∧ ∀ z∈N, z≠y → ¬E z u

inductive ClawVertex
  | center
  | middle (i : Fin 3)
  | tip (i : Fin 3)
  deriving DecidableEq

def ClawVertex.adj : ClawVertex → ClawVertex → Prop
  | .center, .middle _ | .middle _, .center => True
  | .middle i, .tip j | .tip j, .middle i => i=j
  | _, _ => False

def InducedClaw (E : Edge) (S : Vertices) : Prop :=
  ∃ f : ClawVertex → ℕ, (∀ v, f v∈S) ∧ Function.Injective f ∧
    ∀ v w, E (f v) (f w) ↔ ClawVertex.adj v w

def Captures (E : Edge) (T : Vertices) : ℕ → Vertices → Prop
  | 0, _ => True
  | m+1, S => ∃ x, Legal E S x ∧ ∀ y, Legal E (S.erase x) y →
      y∉T ∧ Captures E T m ((S.erase x).erase y)

def Wins (E : Edge) (w : ℕ → ℝ) : ℕ → Vertices → ℝ → Prop
  | 0, _, g => g≤0
  | m+1, S, g => ∃ x, Legal E S x ∧ ∀ y, Legal E (S.erase x) y →
      Wins E w m ((S.erase x).erase y) (g-w x+w y)

theorem capture_color {E : Edge} (sym : Undirected E) {col : ℕ → Bool}
    (bip : ∀ ⦃u v⦄, E u v → col u≠col v) (k : Bool) (T : Vertices)
    (same : ∀ x∈T, col x=k) (m : ℕ) (S : Vertices) (size : S.card=2*m)
    (conn : Connected E S) (free : ¬LongClaw E S)
    (unique : ∀ x∈T, Legal E S x → ∀ y∈T, Legal E S y → x=y) :
    Captures E T m S := by sorry

theorem win_equal_positive_edges {E : Edge} (sym : Undirected E) {col : ℕ → Bool}
    (bip : ∀ ⦃u v⦄, E u v → col u≠col v) (w : ℕ → ℝ) (nn : ∀ x,0≤w x)
    (m : ℕ) (S : Vertices) (size : S.card=2*m) (conn : Connected E S)
    (free : ¬InducedClaw E S)
    (equal : ∀ x∈S, ∀ y∈S, E x y → 0<w x → 0<w y → w x=w y) :
    Wins E w m S 0 := by sorry

end GraphGrabbing

namespace GraphGrabbing.Comb
open Finset

def Fits (h : ℕ) (L : Finset ℕ) := ∀ i ∈ L, i < h

def flip (n i : ℕ) := n-1-i

def edges (x y : ℕ) : Prop :=
  (x%2=0 ∧ (y=x+1 ∨ y=x+2)) ∨ (y%2=0 ∧ (x=y+1 ∨ x=y+2))

def board (h : ℕ) (L : Finset ℕ) : Vertices :=
  (range h).image (fun i => 2*i) ∪ L.image (fun i => 2*i+1)

def RootLegal (S : Vertices) (z : ℕ) :=
  Legal edges S z ∧ (S.erase z=∅ ∨ 0∈S.erase z)

def weight (u w : ℕ → ℝ) (z : ℕ) : ℝ := if z%2=0 then u (z/2) else w (z/2)

noncomputable def rootMoves (S : Vertices) : Vertices := by
  classical exact S.filter (RootLegal S)

noncomputable def rootedValue (w : ℕ → ℝ) : ℕ → Vertices → ℝ
  | 0, _ => 0
  | f+1, S => if ne : (rootMoves S).Nonempty then
      (rootMoves S).sup' ne fun z => w z-rootedValue w f (S.erase z)
    else 0

theorem opposite_rooted_values (u w : ℕ → ℝ) {n L} (fit : Fits n L)
    (even : n%2=0) (evenLeaves : L.card%2=0) (top : n-1∈L)
    (minimum : ∀ i∈L,w (n-1)≤w i) (nn : ∀ i∈L,0≤w i) :
    0 ≤ rootedValue (weight u w) (n+L.card) (board n L) +
        rootedValue (weight (u ∘ flip n) (w ∘ flip n)) (n+(L.image (flip n)).card)
          (board n (L.image (flip n))) := by sorry

end GraphGrabbing.Comb
