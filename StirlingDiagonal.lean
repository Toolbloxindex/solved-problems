module

public import Std

@[expose] public section

namespace StirlingDiagonal

/-- Coefficient of q^d in [1]_q + [3]_q + ... + [2*n-1]_q.
On k=n-1 this is both type B polynomials, by Sagan-Swanson, Theorem 2.1. -/
def coeff : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, d => coeff n d + (if d < 2*n+1 then 1 else 0)

theorem coeff_formula (n d : Nat) : coeff n d = n - (d+1)/2 := by
  induction n with
  | zero => simp [coeff]
  | succ n ih =>
    simp only [coeff, ih]
    split <;> omega

/-- Every interior stride-two triple on the diagonal has gap exactly one. -/
theorem parity_gap (n d : Nat) (h : d+4 < 2*n-1) :
    coeff n (d+2) * coeff n (d+2) = coeff n d * coeff n (d+4) + 1 := by
  simp only [coeff_formula]
  let v := n - (d+4+1)/2
  have h0 : n - (d+1)/2 = v+2 := by dsimp [v]; omega
  have h2 : n - (d+2+1)/2 = v+1 := by dsimp [v]; omega
  rw [h0, h2]
  change (v+1)*(v+1) = (v+2)*v+1
  simp [Nat.add_mul, Nat.mul_add] <;> omega

#print axioms StirlingDiagonal.parity_gap

end StirlingDiagonal
