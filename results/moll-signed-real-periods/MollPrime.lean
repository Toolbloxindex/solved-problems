import MollRigidity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace MollRigidity
open Finset Polynomial
open scoped QuadraticAlgebra

theorem state_prod (R : Type*) [CommRing R] (n : ℕ) :
    state R n = ∏ k ∈ range n, factor R (k+1) := by
  induction n with
  | zero => simp [state]
  | succ n ih => rw [state, prod_range_succ, ih]

private theorem universal_prod {p : ℕ} [Fact p.Prime] (x : Gauss (ZMod p)) :
    ∏ a : ZMod p, (x - algebraMap (ZMod p) _ a) = x^p - x := by
  let P : (ZMod p)[X] := X^p-X
  have hs : P.Splits := Polynomial.splits_X_pow_char_sub_X _ p
  have hm : P.Monic := monic_X_pow_sub (by simpa using (Fact.out : p.Prime).one_lt)
  have hr : P.roots = (univ : Finset (ZMod p)).val := by
    simpa [P] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have h := hs.eq_prod_roots_of_monic hm
  rw [hr] at h
  change P = ∏ a : ZMod p, (X-C a) at h
  have he := congrArg (aeval x) h
  simpa [P] using he.symm

private def residueEquiv (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun k := (k.val : ZMod p)
  invFun k := ⟨k.val, k.val_lt⟩
  left_inv k := Fin.ext (ZMod.val_natCast_of_lt k.isLt)
  right_inv := ZMod.natCast_zmod_val

private def iota (R : Type*) [CommRing R] : Gauss R := ⟨0,1⟩

private theorem iota_sq (R : Type*) [CommRing R] : iota R ^ 2 = -1 := by
  ext <;> simp [iota, pow_two]

private theorem iota_pow (R : Type*) [CommRing R] (n : ℕ) : iota R ^ n = iota R ^ (n%4) := by
  have h4 : iota R ^ 4 = 1 := by calc
    iota R ^ 4 = (iota R ^ 2)^2 := by ring
    _ = 1 := by rw [iota_sq]; ring
  calc
    iota R ^ n = iota R ^ (4*(n/4)+n%4) := by rw [Nat.div_add_mod]
    _ = _ := by rw [pow_add,pow_mul,h4,one_pow,one_mul]

private theorem block_prime_eval (p : ℕ) [Fact p.Prime] :
    state (ZMod p) p = iota (ZMod p)^p * (iota (ZMod p)^p - iota (ZMod p)) := by
  let i := iota (ZMod p)
  let g (a : ZMod p) := i*(i-algebraMap (ZMod p) _ a)
  have hf (k : ℕ) : factor (ZMod p) (k+1) = g ((k:ZMod p)+1) := by
    ext <;> simp [factor,g,i,iota]
  rw [state_prod, Finset.prod_range]
  simp_rw [hf]
  have he : (∏ k : Fin p, g ((k.val:ZMod p)+1)) = ∏ a : ZMod p, g a :=
    Fintype.prod_equiv ((residueEquiv p).trans (Equiv.addRight 1)) _ _ (fun _ => rfl)
  rw [he]
  simp only [g, prod_mul_distrib, prod_const, card_univ, ZMod.card, universal_prod, i]

/-- The signed complete block is -2 at every prime congruent to 3 modulo 4. -/
theorem block_prime {p : ℕ} [Fact p.Prime] (hp : p%4 = 3) :
    state (ZMod p) p = -2 := by
  rw [block_prime_eval, iota_pow (ZMod p) p, hp]
  have h3 : iota (ZMod p)^3 = -iota (ZMod p) := by rw [pow_succ,iota_sq]; ring
  rw [h3]
  calc
    _ = 2*iota (ZMod p)^2 := by ring
    _ = -2 := by rw [iota_sq]; ring

theorem block_prime_split {p : ℕ} [Fact p.Prime] (hp : p%4 = 1) :
    state (ZMod p) p = 0 := by
  rw [block_prime_eval, iota_pow (ZMod p) p, hp, pow_one, sub_self, mul_zero]

theorem prime_period_iff {p t : ℕ} [Fact p.Prime] (hp : p%4 = 3) :
    Function.Periodic (fun n => (moll n : ZMod p)) t ↔
      p * orderOf (-2 : ZMod p) ∣ t := by
  have ho : Odd p := ⟨p/2, by omega⟩
  rw [period_iff ho, block_prime hp]
  have h := orderOf_injective (algebraMap (ZMod p) (Gauss (ZMod p))).toMonoidHom
    QuadraticAlgebra.algebraMap_injective (-2)
  change orderOf (algebraMap (ZMod p) (Gauss (ZMod p)) (-2)) = _ at h
  rw [map_neg, map_ofNat] at h
  rw [h]

end MollRigidity
