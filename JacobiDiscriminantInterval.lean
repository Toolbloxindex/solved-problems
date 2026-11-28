module

public import JacobiDiagonalControls

@[expose] public section

namespace JacobiDiscriminantInterval

open JacobiDiagonalControls

theorem disc_mid_pos {u : ℝ} (hl : -1 ≤ u) (hr : u ≤ 2) :
    0 < disc u := by
  let t : ℝ := (u+1)/3
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hs : 0 ≤ 1-t := by dsimp [t]; linarith
  have h : disc u =
      6144*(1-t)^6 + 113664*t*(1-t)^5 + 312576*t^2*(1-t)^4 +
      754944*t^3*(1-t)^3 + 676992*t^4*(1-t)^2 + 663360*t^5*(1-t) + 11376*t^6 := by
    dsimp [t, disc, cubicDisc]
    ring
  rw [h]
  by_cases hzero : t = 0
  · simp [hzero]
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    positivity

theorem disc_right_strict {x y : ℝ} (hx : 2 ≤ x) (hxy : x < y) :
    disc y < disc x := by
  rw [show x = 2+(x-2) by ring, show y = 2+(y-2) by ring, disc_pos_shift, disc_pos_shift]
  have hx' : 0 ≤ x-2 := sub_nonneg.mpr hx
  have hxy' : x-2 ≤ y-2 := sub_le_sub_right hxy.le 2
  have hp (n : ℕ) : (x-2)^n ≤ (y-2)^n := pow_le_pow_left₀ hx' hxy' n
  linarith only [hxy, hp 2, hp 3, hp 4, hp 5, hp 6]

theorem disc_left_strict {x y : ℝ} (hy : y ≤ -1) (hxy : x < y) :
    disc x < disc y := by
  rw [show x = -1-(-1-x) by ring, show y = -1-(-1-y) by ring, disc_neg_shift, disc_neg_shift]
  have hy' : 0 ≤ -1-y := sub_nonneg.mpr hy
  have hxy' : -1-y ≤ -1-x := sub_le_sub_left hxy.le (-1)
  have hp (n : ℕ) : (-1-y)^n ≤ (-1-x)^n := pow_le_pow_left₀ hy' hxy' n
  linarith only [hxy, hp 2, hp 3, hp 4, hp 5, hp 6]

/-- Once the two endpoint equations are checked, no other component of the discriminant
superlevel set can occur. -/
theorem disc_nonneg_iff_between {left right : ℝ} (hl : left ≤ -1) (hr : 2 ≤ right)
    (hleft : disc left = 0) (hright : disc right = 0) (u : ℝ) :
    0 ≤ disc u ↔ left ≤ u ∧ u ≤ right := by
  constructor
  · intro hu
    constructor
    · by_contra! hut
      have h := disc_left_strict hl hut
      linarith
    · by_contra! hut
      have h := disc_right_strict hr hut
      linarith
  · rintro ⟨hlu, hur⟩
    rcases lt_trichotomy u (-1) with hum | hum | hum
    · rcases hlu.eq_or_lt with h | h
      · rw [← h, hleft]
      · have h' := disc_left_strict hum.le h
        linarith
    · exact (disc_mid_pos hum.ge (by linarith)).le
    · by_cases hu : u ≤ 2
      · exact (disc_mid_pos hum.le hu).le
      · rcases hur.eq_or_lt with h | h
        · rw [h, hright]
        · have h' := disc_right_strict (le_of_not_ge hu) h
          linarith

end JacobiDiscriminantInterval
