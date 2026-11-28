module

public import Ribbons

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

private def rank (x : Weight) : ℤ :=
  let ⟨a, b, c, d, e⟩ := x
  a + 2 * b + 3 * c + 4 * d + 5 * e

private theorem rank_mono {x y : Weight} (h : tilted x y) : rank x ≤ rank y := by
  rcases x with ⟨a, b, c, d, e⟩
  rcases y with ⟨f, g, i, j, k⟩
  simp only [rank, tilted] at *
  omega

private theorem equal_of_equal_rank {x y : Weight} (h : tilted x y) (he : rank x = rank y) :
    x = y := by
  rcases x with ⟨a, b, c, d, e⟩
  rcases y with ⟨f, g, i, j, k⟩
  simp only [rank, tilted, Prod.mk.injEq] at *
  omega

private def toWeight (x : Point) : Weight :=
  let ⟨a, b, c, d, e⟩ := x
  (a.val, b.val, c.val, d.val, e.val)

private theorem toWeight_injective : Function.Injective toWeight := by
  rintro ⟨a, b, c, d, e⟩ ⟨f, g, h, i, j⟩ hxy
  simpa [toWeight, Fin.ext_iff, Int.ofNat_inj] using hxy

private theorem box_has_preimage {x : Weight} (hx : box x) : ∃ y, toWeight y = x := by
  rcases x with ⟨a, b, c, d, e⟩
  simp only [box] at hx
  refine ⟨(⟨a.toNat, by omega⟩, ⟨b.toNat, by omega⟩, ⟨c.toNat, by omega⟩,
    ⟨d.toNat, by omega⟩, ⟨e.toNat, by omega⟩), ?_⟩
  simp only [toWeight, Prod.mk.injEq]
  omega

private theorem mem_iff (x : Point) (prior c : ℤ) :
    toWeight x ∈ latticeSlice prior c ↔ prior < (total x : ℤ) ∧ (total x : ℤ) ≤ c := by
  change (box (toWeight x) ∧ prior < weightSum (toWeight x) ∧ weightSum (toWeight x) ≤ c) ↔
    (prior < (total x : ℤ) ∧ (total x : ℤ) ≤ c)
  rcases x with ⟨a, b, c₀, d, e⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := c₀.isLt
  have hd := d.isLt
  have he := e.isLt
  simp only [box, toWeight, weightSum, total, suffix, Int.natCast_add]
  omega

private theorem tilted_iff (x y : Point) : tilted (toWeight x) (toWeight y) ↔ suffixLE x y := by
  rcases x with ⟨a, b, c, d, e⟩
  rcases y with ⟨f, g, h, i, j⟩
  simp only [tilted, toWeight, suffixLE, suffix]
  omega

private theorem toWeight_rank (x : Point) : rank (toWeight x) = (height x : ℤ) := by
  rcases x with ⟨a, b, c, d, e⟩
  simp only [rank, toWeight, height, suffix]
  omega

private theorem toWeight_cover {prior c : ℤ} {x y : Point}
    (h : Cover {p | prior < (total p : ℤ) ∧ (total p : ℤ) ≤ c} x y ∧
      height y = height x + 1) :
    covers (latticeSlice prior c) (toWeight x) (toWeight y) := by
  obtain ⟨⟨hx, hy, hne, hle, _⟩, hstep⟩ := h
  refine ⟨(mem_iff x prior c).mpr hx, (mem_iff y prior c).mpr hy,
    fun h => hne (toWeight_injective h), (tilted_iff x y).mpr hle, ?_⟩
  intro z hxz hzy
  have hxrank := rank_mono hxz
  have hyrank := rank_mono hzy
  have hr : rank (toWeight y) = rank (toWeight x) + 1 := by
    rw [toWeight_rank, toWeight_rank]
    omega
  by_cases he : rank (toWeight x) = rank z
  · exact Or.inl (equal_of_equal_rank hxz he).symm
  · exact Or.inr (equal_of_equal_rank hzy (by omega))

/-- Literal source statement on integer lattice points, with explicit box inequalities. -/
theorem conjecture_10_2_integer_coordinates (c prior : ℤ)
    (hc₁ : 1 ≤ c) (hc₂ : c ≤ 25) (hc : Int.gcd 6 c = 1)
    (hp : Int.gcd 6 prior = 1) (hpc : prior < c)
    (hmax : ∀ d : ℤ, d < c → Int.gcd 6 d = 1 → d ≤ prior) :
    ∃ ribbons : List (List Weight),
      ribbons.flatten.Nodup ∧
      (∀ x : Weight, x ∈ ribbons.flatten ↔ x ∈ latticeSlice prior c) ∧
      ∀ r ∈ ribbons, r.length = 6 ∧ r.IsChain (covers (latticeSlice prior c)) := by
  simp only [Int.gcd_comm 6] at hc hp hmax
  obtain ⟨ribbons, hdup, hmem, hribbons⟩ :=
    conjecture_10_2_a6 c prior hc₁ (by simpa using hc₂) hc hpc hp hmax
  let lifted := ribbons.map (List.map toWeight)
  have hflat : lifted.flatten = ribbons.flatten.map toWeight := List.map_flatten.symm
  refine ⟨lifted, ?_, ?_, ?_⟩
  · rw [hflat]
    exact hdup.map toWeight_injective
  · intro x
    rw [hflat, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_iff y prior c).mpr ((hmem y).mp hy)
    · intro hx
      obtain ⟨y, rfl⟩ := box_has_preimage hx.1
      exact ⟨y, (hmem y).mpr ((mem_iff y prior c).mp hx), rfl⟩
  · intro r hr
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hlen, hchain⟩ := hribbons row hrow
    exact ⟨by simpa using hlen, List.isChain_map_of_isChain toWeight
      (fun _ _ => toWeight_cover) hchain⟩

#print axioms ArmstrongRibbons.conjecture_10_2_a6
#print axioms conjecture_10_2_integer_coordinates

end ArmstrongRibbons.SourceAudit
