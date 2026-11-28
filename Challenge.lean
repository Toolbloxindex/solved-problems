module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup

@[expose] public section

namespace ArmstrongRibbons.SourceAudit

abbrev Weight := ℤ × ℤ × ℤ × ℤ × ℤ

def box (x : Weight) : Prop :=
  let ⟨a, b, c, d, e⟩ := x
  (0 ≤ a ∧ a < 6) ∧ (0 ≤ b ∧ b < 6) ∧ (0 ≤ c ∧ c < 6) ∧
    (0 ≤ d ∧ d < 6) ∧ (0 ≤ e ∧ e < 6)

def weightSum (x : Weight) : ℤ :=
  let ⟨a, b, c, d, e⟩ := x
  a + b + c + d + e

def latticeSlice (prior c : ℤ) : Set Weight :=
  {x | box x ∧ prior < weightSum x ∧ weightSum x ≤ c}

def tilted (x y : Weight) : Prop :=
  let ⟨a, b, c, d, e⟩ := x
  let ⟨f, g, h, i, j⟩ := y
  e ≤ j ∧ d + e ≤ i + j ∧ c + d + e ≤ h + i + j ∧
    b + c + d + e ≤ g + h + i + j ∧ a + b + c + d + e ≤ f + g + h + i + j

def covers (S : Set Weight) (x y : Weight) : Prop :=
  x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ tilted x y ∧
    ∀ z, tilted x z → tilted z y → z = x ∨ z = y

theorem conjecture_10_2_integer_coordinates (c prior : ℤ)
    (hc₁ : 1 ≤ c) (hc₂ : c ≤ 25) (hc : Int.gcd 6 c = 1)
    (hp : Int.gcd 6 prior = 1) (hpc : prior < c)
    (hmax : ∀ d : ℤ, d < c → Int.gcd 6 d = 1 → d ≤ prior) :
    ∃ ribbons : List (List Weight),
      ribbons.flatten.Nodup ∧
      (∀ x : Weight, x ∈ ribbons.flatten ↔ x ∈ latticeSlice prior c) ∧
      ∀ r ∈ ribbons, r.length = 6 ∧ r.IsChain (covers (latticeSlice prior c)) := by sorry

end ArmstrongRibbons.SourceAudit
