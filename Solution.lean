module

public import PeriodFourProof

@[expose] public section

namespace PalomarSongsuwan
open KaylesRays.PeriodFourGraph

/-- Exact scores for two unbounded residue classes on the same host. -/
theorem values (j : Nat) : score (4*j+5) = 8 ∧ score (4*j+7) = 9 := by
  exact KaylesRays.PeriodFourGraph.counterexample_values j

/-- The sequence of literal game values has no eventual period of two. -/
theorem no_period_two : ¬∃ n : Nat, ∀ k≥n, score (k+2) = score k := by
  exact KaylesRays.PeriodFourGraph.songsuwan_conjecture_2_false

end PalomarSongsuwan
