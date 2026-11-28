import GameValue
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

namespace KaylesRays.PeriodFourGraph
open LiteralKayles

/-- Small literal factors and their disjoint unions and complete joins. -/
inductive Factor where
  | bits (order mask : Nat)
  | path (order : Nat)
  | cycle (order : Nat)
  | combine (joined : Bool) (left right : Factor)

def Factor.order : Factor → Nat
  | .bits n _ | .path n | .cycle n => n
  | .combine _ l r => l.order+r.order

def Factor.edge : Factor → Nat → Nat → Bool
  | .bits _ m, i, j =>
    let hi := max i j
    let lo := min i j
    decide (i≠j) && m.testBit (hi*(hi-1)/2+lo)
  | .path _, i, j => decide (i+1=j ∨ j+1=i)
  | .cycle n, i, j =>
    decide (i+1=j ∨ j+1=i ∨ (i=0 ∧ j=n-1) ∨ (j=0 ∧ i=n-1))
  | .combine joined l r, i, j =>
    if i<l.order then
      if j<l.order then l.edge i j else joined
    else if j<l.order then joined else r.edge (i-l.order) (j-l.order)

private def jn := Factor.combine true
private def dj := Factor.combine false
private def one := Factor.path 1
private def fork := jn (.bits 6 2353) one
private def endBit := jn (.bits 6 1110) one

def modules : List Factor :=
  [.bits 5 20,
    dj (jn (dj one (dj (.bits 4 3) (.path 3))) one) (.cycle 16),
    dj fork (.cycle 18),
    dj (jn (dj one (.cycle 6)) (.bits 4 3)) (.cycle 35),
    dj (jn (.bits 6 1174) one) (jn (.cycle 35) (jn (.cycle 18) (.cycle 16))),
    dj fork (dj endBit endBit),
    dj (.cycle 78) (.path 3)]

def joinedCore := modules.foldr jn (.path 0)

def hub : Fin 291 := 279

private def seesHub (i : Nat) : Prop :=
  (i<279 ∧ i∉[0,5,30,55,101,177,198]) ∨ i∈[280,281,282,285,288]

private instance (i : Nat) : Decidable (seesHub i) :=
  inferInstanceAs (Decidable ((i<279 ∧ i∉[0,5,30,55,101,177,198]) ∨ i∈[280,281,282,285,288]))

/-- The core's fixed leaves are 280 and 281. Its three fixed P3 branches
have labels 282–284, 285–287 and 288–290. -/
def hostEdge (a b : Fin 291) : Bool :=
  let i := a.val
  let j := b.val
  if i<279 ∧ j<279 then joinedCore.edge i j
  else decide ((i=279 ∧ seesHub j) ∨ (j=279 ∧ seesHub i)) ||
    [282,285,288].any (fun k => decide (k≤i ∧ i<k+3 ∧ k≤j ∧ j<k+3 ∧ (i+1=j ∨ j+1=i)))

inductive Vertex where
  | old (v : Fin 291)
  | ray (n : Nat) (i : Fin 5)
deriving DecidableEq

def edge : Vertex → Vertex → Bool
  | .old a, .old b => hostEdge a b
  | .old a, .ray _ i | .ray _ i, .old a => decide (a=hub ∧ i=0)
  | .ray k i, .ray l j => decide (k=l ∧ (i.val+1=j.val ∨ j.val+1=i.val))

/-- These are exactly the old vertices and the five fresh path vertices for
each index smaller than x. Only their endpoints receive a hub edge. -/
def board (x : Nat) : Finset Vertex :=
  Finset.univ.image Vertex.old ∪
    (Finset.range x).biUnion (fun k => Finset.univ.image (Vertex.ray k))

def score (x : Nat) : Nat := value edge (board x)

def CounterexampleValues : Prop :=
  ∀ j : Nat, score (4*j+5)=8 ∧ score (4*j+7)=9

theorem not_period_two (values : CounterexampleValues) :
    ¬∃ b : Nat, ∀ k≥b, score (k+2)=score k := by
  rintro ⟨b,tail⟩
  have e := tail (4*b+5) (by omega)
  obtain ⟨a,c⟩ := values b
  rw [show 4*b+5+2=4*b+7 by omega,c,a] at e
  contradiction

end KaylesRays.PeriodFourGraph

#print axioms KaylesRays.PeriodFourGraph.not_period_two
