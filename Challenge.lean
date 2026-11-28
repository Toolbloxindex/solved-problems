module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace PalomarArmstrong

/-- Weakly decreasing nonnegative suffix sums starting with two. -/
def Diagram (n : ℕ) (y : Fin (2*n) → ℕ) : Prop :=
  Antitone y ∧ ∀ h, h.val = 0 → y h = 2

/-- Adjacent tilted vectors differ by one unit in exactly one row. -/
def UnitStep {n : ℕ} (before after : Fin (2*n) → ℕ) : Prop :=
  ∃ row, ∀ h, after h = before h + if h = row then 1 else 0

theorem c2_ribbon_partition (n : ℕ) (hn : 0 < n) :
    ∃ ribbons : Fin n → Fin (2*n+1) → Fin (2*n) → ℕ,
      (∀ t k, Diagram n (ribbons t k)) ∧
      (∀ y, Diagram n y → ∃! p : Fin n × Fin (2*n+1), ribbons p.1 p.2 = y) ∧
      ∀ t (u v : Fin (2*n+1)), v.val = u.val + 1 → UnitStep (ribbons t u) (ribbons t v) := by
  sorry

end PalomarArmstrong
