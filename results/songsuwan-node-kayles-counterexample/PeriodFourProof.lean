import PeriodFourRealization

namespace KaylesRays.PeriodFourGraph
open PeriodFourRealization PeriodFourLiteral MixedPaths

private theorem fixed_score (x : Nat) :
    PeriodFourGraph.score x = literalProfile 0 (x : Int) 3 false := by
  obtain ⟨a,b,c⟩ := canonical_counts x
  change count (canonicalIds x) canonicalKind 5=x at a
  change count (canonicalIds x) canonicalKind 3=3 at b
  change count (canonicalIds x) canonicalKind 1=2 at c
  rw [score_eq_mixed,← hostBoard_zero]
  change MixedPaths.score coreAdj none (hostBoard 0) (canonicalIds x) (arms canonicalKind) = _
  rw [mixed_eq_profile _ _ _ (canonical_live x) (c.symm ▸ (by decide : 0<(2:Nat))),a,b,c]
  exact (literal_eq_profile 0 (by decide) x 3 false (by omega) (by decide)).symm

/-- The scores of the two unbounded residue classes on the literal graph. -/
theorem counterexample_values : CounterexampleValues := by
  intro j
  obtain ⟨a,b⟩ := PeriodFour.witness_recurrence literalProfile literal_rule j
  have e : ((4*j+5:Nat):Int)=4*(j:Int)+5 := by omega
  have f : ((4*j+7:Nat):Int)=4*(j:Int)+7 := by omega
  rw [fixed_score _,fixed_score _,e,f]
  exact ⟨a,b⟩

/-- For this single fixed host, lag two fails arbitrarily late. -/
theorem songsuwan_conjecture_2_false :
    ¬∃ n : Nat, ∀ k≥n, PeriodFourGraph.score (k+2)=PeriodFourGraph.score k :=
  not_period_two counterexample_values

end KaylesRays.PeriodFourGraph
