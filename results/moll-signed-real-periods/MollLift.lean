import MollPrime
import Mathlib.Algebra.CharP.Lemmas

namespace MollRigidity
open Finset
open scoped QuadraticAlgebra

private theorem prod_chunks {R : Type*} [CommMonoid R] (f : ℕ → R) (p q : ℕ) :
    ∏ k ∈ range (p*q), f k = ∏ t ∈ range p, ∏ j ∈ range q, f (t*q+j) := by
  induction p with
  | zero => simp
  | succ p ih => rw [Nat.succ_mul, prod_range_add, prod_range_succ, ih]

private theorem linear_prod {R : Type*} [CommRing R] (a x : R) (hx : x^2=0) (n : ℕ) :
    ∏ t ∈ range (n+1), (a + (t:R)*x) =
      a^(n+1) + ((∑ t ∈ range (n+1), t : ℕ) : R)*a^n*x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, sum_range_succ _ (n+1)]
    push_cast
    linear_combination ((∑ t ∈ range (n+1), (t:R))*a^n*((n:R)+1))*hx

private theorem residue_lift_prod {R : Type*} [CommRing R] (p : ℕ) (ho : Odd p)
    (a x : R) (hx : x^2=0) (hp : (p:R)*x=0) :
    ∏ t ∈ range p, (a + (t:R)*x) = a^p := by
  obtain ⟨k,rfl⟩ := ho
  have inter : (∑ t ∈ range (2*k+1), t) = (2*k+1)*k := by
    rw [sum_range_id]
    have he : (2*k+1)*(2*k+1-1) = ((2*k+1)*k)*2 := by
      rw [show 2*k+1-1 = 2*k by omega]; ring
    rw [he, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  rw [linear_prod a x hx (2*k), inter]
  push_cast at hp ⊢
  linear_combination (k:R)*a^(2*k)*hp

private theorem lift_block (p q : ℕ) (ho : Odd p) (hq : p ∣ q) :
    state (ZMod (p*q)) (p*q) = state (ZMod (p*q)) q ^ p := by
  let R := Gauss (ZMod (p*q))
  let i : R := ⟨0,-1⟩
  have hpq : (p:R)*(q:R)=0 := by
    rw [← Nat.cast_mul]
    exact QuadraticAlgebra.ext (ZMod.natCast_self _) rfl
  obtain ⟨b,hb⟩ := hq
  have hbc : (q:R) = (p:R)*(b:R) := by
    simpa only [Nat.cast_mul] using congrArg (fun k : ℕ => (k:R)) hb
  have hqq : (q:R)^2=0 := by
    calc (q:R)^2 = ((p:R)*(q:R))*(b:R) := by rw [hbc]; ring
         _ = 0 := by rw [hpq, zero_mul]
  have hx : ((q:R)*i)^2=0 := by rw [mul_pow, hqq, zero_mul]
  have hp : (p:R)*((q:R)*i)=0 := by rw [← mul_assoc, hpq, zero_mul]
  have hf (t j : ℕ) : factor (ZMod (p*q)) (t*q+j+1) =
      factor (ZMod (p*q)) (j+1) + (t:R)*((q:R)*i) := by
    ext <;> simp [factor, i, R] ; ring
  simp only [state_prod]
  rw [prod_chunks, prod_comm]
  simp_rw [hf, residue_lift_prod p ho _ _ hx hp]
  rw [prod_pow]

def reduceGauss (q : ℕ) : Gauss ℤ →+* Gauss (ZMod q) where
  toFun x := ⟨x.re,x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

theorem reduce_state (q n : ℕ) : reduceGauss q (state ℤ n) = state (ZMod q) n := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    change reduceGauss q (state ℤ n * _) = state (ZMod q) n * _
    rw [map_mul, ih]
    congr 1
    ext <;> simp [reduceGauss, factor]

theorem reduce_zero (q : ℕ) (x : Gauss ℤ) :
    reduceGauss q x = 0 ↔ (q:Gauss ℤ) ∣ x := by
  constructor
  · intro h
    obtain ⟨u,hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.re q).mp (congrArg QuadraticAlgebra.re h)
    obtain ⟨v,hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.im q).mp (congrArg QuadraticAlgebra.im h)
    exact ⟨⟨u,v⟩, by ext <;> simp [hu,hv]⟩
  · rintro ⟨y,rfl⟩
    rw [map_mul, map_natCast]
    have : (q:Gauss (ZMod q))=0 := by ext <;> simp
    rw [this, zero_mul]

private theorem lift_power {R : Type*} [CommRing R] (p q : ℕ) (hp : p.Prime) (hq : p ∣ q)
    (x y : R) (h : (q:R) ∣ x-y) : ((q*p:ℕ):R) ∣ x^p-y^p := by
  obtain ⟨u,hu⟩ := h
  rw [show x = (q:R)*u+y by rw [← hu]; ring]
  apply hp.dvd_add_pow_sub_pow_of_dvd
  · obtain ⟨k,hk⟩ := hq
    have hdiv : ((q*p:ℕ):R) ∣ ((q:R)*u)^2 :=
      ⟨(k:R)*u^2, by rw [hk]; push_cast; ring⟩
    exact hdiv.trans (pow_dvd_pow _ hp.two_le)
  · exact ⟨u, by push_cast; ring⟩

/-- The specialization at i of the Cárdenas–Lluis block congruence. -/
theorem inert_block {p : ℕ} [Fact p.Prime] (hp : p%4=3) (e : ℕ) :
    state (ZMod (p^(e+1))) (p^(e+1)) = (-2)^(p^e) := by
  induction e with
  | zero =>
    rw [Nat.zero_add, pow_one, pow_zero, pow_one]
    exact block_prime hp
  | succ e ih =>
    let q := p^(e+1)
    have hq : p ∣ q := dvd_pow_self _ (by omega)
    have ho : Odd p := ⟨p/2, by omega⟩
    have hy : (q:Gauss ℤ) ∣ state ℤ q - (-2)^(p^e) := by
      apply (reduce_zero q _).mp
      rw [map_sub, map_pow, map_neg, map_ofNat, reduce_state, sub_eq_zero]
      exact ih
    have hz := lift_power p q Fact.out hq _ _ hy
    have he := (reduce_zero (q*p) _).mpr hz
    simp only [map_sub, map_pow, map_neg, map_ofNat, reduce_state, sub_eq_zero] at he
    rw [show p^(e+1+1) = p*q by simp [q,pow_succ'] , lift_block p q ho hq]
    rw [mul_comm p q]
    simpa [pow_succ, pow_mul] using he


private theorem lift_root (a : ℤ) {p : ℕ} (hp : p.Prime) (k e : ℕ)
    (hk : (a:ZMod p)^k = 1) :
    ((a:ZMod (p^(e+1)))^(p^e))^k = 1 := by
  have h (b : ℕ) : ((p^(b+1):ℕ):ℤ) ∣ (a^k)^(p^b)-1 := by
    induction b with
    | zero =>
      rw [Nat.zero_add, pow_one, pow_zero, pow_one]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa using sub_eq_zero.mpr hk
    | succ b ih =>
      have hq : p ∣ p^(b+1) := dvd_pow_self _ (by omega)
      have hz := lift_power p (p^(b+1)) hp hq ((a^k)^(p^b)) 1 ih
      simpa [pow_succ, pow_mul] using hz
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h e)
  push_cast at he
  rw [pow_right_comm, ← sub_eq_zero]
  exact he

/-- All periods of the original signed real coordinate, for an inert prime power. -/
theorem primePower_period_iff {p t : ℕ} [Fact p.Prime] (hp : p%4 = 3) (e : ℕ) :
    Function.Periodic (fun n => (moll n : ZMod (p^(e+1)))) t ↔
      p^(e+1) * orderOf (-2 : ZMod p) ∣ t := by
  have ho : Odd p := ⟨p/2, by omega⟩
  rw [period_iff (ho.pow), inert_block hp]
  let q := p^(e+1)
  let z : ZMod q := (-2)^(p^e)
  have hz : orderOf ((-2 : Gauss (ZMod q))^(p^e)) = orderOf z := by
    have hi := orderOf_injective (algebraMap (ZMod q) (Gauss (ZMod q))).toMonoidHom
      QuadraticAlgebra.algebraMap_injective z
    change orderOf (algebraMap (ZMod q) (Gauss (ZMod q)) ((-2)^(p^e))) = _ at hi
    rw [map_pow, map_neg, map_ofNat] at hi
    exact hi
  have hq : p ∣ q := dvd_pow_self _ (by omega)
  have he : orderOf z = orderOf (-2 : ZMod p) := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      have h := lift_root (-2) (Fact.out : p.Prime) (orderOf (-2 : ZMod p)) e
      have hc (m : ℕ) : ((-2:ℤ):ZMod m) = -2 := by norm_num
      rw [hc p, hc (p^(e+1))] at h
      exact h (pow_orderOf_eq_one _)
    · apply orderOf_dvd_of_pow_eq_one
      have h := congrArg (ZMod.castHom hq (ZMod p)) (pow_orderOf_eq_one z)
      simpa only [map_pow, z, map_neg, map_ofNat, ZMod.pow_card_pow, map_one] using h
  change q * orderOf ((-2 : Gauss (ZMod q))^(p^e)) ∣ t ↔ _
  rw [hz,he]


/-- The least positive period of the signed real coordinate from index zero. -/
theorem least_inert_period {p : ℕ} [Fact p.Prime] (hp : p%4 = 3) (e : ℕ) :
    IsLeast {t : ℕ | 0 < t ∧ Function.Periodic (fun n => (moll n : ZMod (p^(e+1)))) t}
      (p^(e+1) * orderOf (-2 : ZMod p)) := by
  have hn : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hd := ZMod.orderOf_dvd_card_sub_one (neg_ne_zero.mpr hn)
  have hprime : p.Prime := Fact.out
  have hpos : 0 < p - 1 := by have := hprime.one_lt; omega
  refine ⟨⟨Nat.mul_pos (pow_pos hprime.pos _) (Nat.pos_of_dvd_of_pos hd hpos),
    (primePower_period_iff hp e).mpr dvd_rfl⟩, ?_⟩
  intro t ht
  exact Nat.le_of_dvd ht.1 ((primePower_period_iff hp e).mp ht.2)

end MollRigidity
