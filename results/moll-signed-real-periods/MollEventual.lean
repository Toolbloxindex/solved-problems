import MollLift
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.Finset

namespace MollRigidity
open Finset
open scoped QuadraticAlgebra

/-- Eventual period, with no stipulated start index. -/
def EventualPeriod (m t : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (moll (n+t) : ZMod m) = (moll n : ZMod m)

private theorem restrict_eventual {m q t : ℕ} (hq : q ∣ m) (h : EventualPeriod m t) :
    EventualPeriod q t := by
  obtain ⟨N,hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  simpa only [map_intCast] using congrArg (ZMod.castHom hq (ZMod q)) (hN n hn)

private theorem inert_eventual_iff {p t : ℕ} [Fact p.Prime] (hp : p%4=3) (e : ℕ) :
    EventualPeriod (p^(e+1)) t ↔ p^(e+1)*orderOf (-2 : ZMod p) ∣ t := by
  constructor
  · rintro ⟨N,hN⟩
    let d := p^(e+1)*orderOf (-2 : ZMod p)
    obtain ⟨hd, hs⟩ := (least_inert_period hp e).1
    have hP : Function.Periodic (fun n => (moll n : ZMod (p^(e+1)))) (N*d) := hs.nat_mul N
    apply (primePower_period_iff hp e).mp
    intro n
    have hl : N ≤ n + N*d := by
      have : N*1 ≤ N*d := Nat.mul_le_mul_left N hd
      omega
    calc
      (moll (n+t) : ZMod (p^(e+1))) = moll (n+t+N*d) := (hP (n+t)).symm
      _ = moll ((n+N*d)+t) := by rw [show n+t+N*d = n+N*d+t by omega]
      _ = moll (n+N*d) := hN _ hl
      _ = moll n := hP n
  · intro h
    exact ⟨0, fun n _ => (primePower_period_iff hp e).mpr h n⟩

private theorem double_block : state (ZMod 2) 2 ^ 2 = 0 := by decide

private theorem noninert_zero {p : ℕ} [Fact p.Prime] (hp : p%4 ≠ 3) (e n : ℕ)
    (hn : p^(e+1)*(2*(e+1)) ≤ n) : (moll n : ZMod (p^(e+1))) = 0 := by
  let q := p^(e+1)
  have hnil : state (ZMod p) p ^ 2 = 0 := by
    by_cases h2 : p=2
    · subst p
      exact double_block
    · have ho := (Fact.out : p.Prime).odd_of_ne_two h2
      have h1 : p % 4 = 1 := by obtain ⟨k,hk⟩ := ho; omega
      rw [block_prime_split h1, zero_pow (by decide)]
  have hdiv : p ∣ q := dvd_pow_self _ (by omega)
  obtain ⟨k,hk⟩ := hdiv
  have hkpos : 0 < k := by
    have hp0 : 0 < q := pow_pos (Fact.out : p.Prime).pos _
    by_contra! nk
    simp [Nat.eq_zero_of_le_zero nk] at hk
    omega
  have hz : state (ZMod p) q ^ 2 = 0 := by
    have hs := blocks p k 0
    simp only [Nat.add_zero, state, mul_one, ←hk] at hs
    rw [hs, pow_right_comm, hnil, zero_pow hkpos.ne']
  have hd : (p:Gauss ℤ) ∣ (state ℤ q)^2 := by
    apply (reduce_zero p _).mp
    simpa only [map_pow, reduce_state] using hz
  have hD : (q:Gauss ℤ) ∣ (state ℤ q)^(2*(e+1)) := by
    simpa only [q, Nat.cast_pow, pow_mul] using pow_dvd_pow_of_dvd hd (e+1)
  have hZ := (reduce_zero q _).mpr hD
  rw [map_pow,reduce_state] at hZ
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hn
  rw [hr, moll_mod, blocks, hZ, zero_mul]
  simp

private theorem eq_of_components {m : ℕ} {a b : ℤ} (h : ∀ p e : ℕ, p.Prime → p^(e+1) ∣ m →
    (a : ZMod (p^(e+1))) = b) : (a : ZMod m) = b := by
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mpr
  apply Int.natAbs_dvd_natAbs.mp
  rw [Int.natAbs_natCast, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hd
  cases k with
  | zero => simp
  | succ e =>
    have hz := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (h p e hp hd)
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hz

/-- Every eventual period is determined by the inert prime powers dividing m. -/
theorem eventual_iff {m t : ℕ} (hm : 0<m) : EventualPeriod m t ↔
    ∀ p e : ℕ, p.Prime → p%4=3 → p^(e+1) ∣ m → p^(e+1)*orderOf (-2 : ZMod p) ∣ t := by
  constructor
  · intro h p e hp hi hd
    let : Fact p.Prime := ⟨hp⟩
    exact (inert_eventual_iff hi e).mp (restrict_eventual hd h)
  · intro h
    refine ⟨m*(2*m), fun n hn => ?_⟩
    apply eq_of_components
    intro p e hp hd
    let : Fact p.Prime := ⟨hp⟩
    by_cases hi : p%4 = 3
    · exact (primePower_period_iff hi e).mpr (h p e hp hi hd) n
    · have hq := Nat.le_of_dvd hm hd
      have hle : e+1 ≤ m :=
        le_trans ((Nat.lt_two_pow_self (n:=e+1)).le.trans (Nat.pow_le_pow_left hp.two_le _)) hq
      have hb := (Nat.mul_le_mul hq (Nat.mul_le_mul_left 2 hle)).trans hn
      rw [noninert_zero hi e _ (hb.trans (Nat.le_add_right _ _)), noninert_zero hi e _ hb]

/-- The lcm over the exact inert prime-power factors of the modulus (empty lcm one). -/
noncomputable def eventualLength (m : ℕ) : ℕ :=
  (m.primeFactors.filter (fun p => p%4=3)).lcm
    (fun p => p^(m.factorization p) * orderOf (-2 : ZMod p))

theorem eventual_period_iff_dvd {m t : ℕ} (hm : 0<m) :
    EventualPeriod m t ↔ eventualLength m ∣ t := by
  rw [eventual_iff hm, eventualLength, Finset.lcm_dvd_iff]
  constructor
  · intro h p hp
    obtain ⟨hmem,hi⟩ := mem_filter.mp hp
    have hpri := Nat.prime_of_mem_primeFactors hmem
    have hfac := (hpri.dvd_iff_one_le_factorization hm.ne').mp (Nat.dvd_of_mem_primeFactors hmem)
    obtain ⟨e,he⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m.factorization p ≠ 0)
    have heq : m.factorization p = e+1 := he
    rw [heq]
    apply h p e hpri hi
    rw [← heq]
    exact Nat.ordProj_dvd _ _
  · intro h p e hp hi hd
    have hpm := (dvd_pow_self p (by omega : e+1 ≠ 0)).trans hd
    have hle := (hp.pow_dvd_iff_le_factorization hm.ne').mp hd
    apply (Nat.mul_dvd_mul_right (pow_dvd_pow p hle) (orderOf (-2 : ZMod p))).trans
    exact h _ (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hpm,hm.ne'⟩,hi⟩)

theorem least_eventual_period {m : ℕ} (hm : 0<m) :
    IsLeast {t : ℕ | 0<t ∧ EventualPeriod m t} (eventualLength m) := by
  have hn : eventualLength m ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro p hp
    obtain ⟨hmem, hi⟩ := mem_filter.mp hp
    have hpri := Nat.prime_of_mem_primeFactors hmem
    let : Fact p.Prime := ⟨hpri⟩
    have hfac := (hpri.dvd_iff_one_le_factorization hm.ne').mp (Nat.dvd_of_mem_primeFactors hmem)
    have he : m.factorization p - 1 + 1 = m.factorization p := by omega
    simpa only [he] using (least_inert_period hi (m.factorization p - 1)).1.1.ne'
  refine ⟨⟨Nat.pos_of_ne_zero hn, (eventual_period_iff_dvd hm).mpr dvd_rfl⟩, ?_⟩
  intro t ht
  exact Nat.le_of_dvd ht.1 ((eventual_period_iff_dvd hm).mp ht.2)

/-- A positive period works from index zero exactly when all prime divisors are inert
and it is an eventual period. -/
theorem pure_period_iff {m t : ℕ} (hm : 0<m) (ht : 0<t) :
    Function.Periodic (fun n => (moll n : ZMod m)) t ↔
      (∀ p ∈ m.primeFactors, p%4 = 3) ∧ eventualLength m ∣ t := by
  constructor
  · intro h
    refine ⟨?_, (eventual_period_iff_dvd hm).mp ⟨0,fun n _ => h n⟩⟩
    intro p hp
    let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    by_contra hi
    have hsub : Function.Periodic (fun n => (moll n : ZMod p)) t := by
      intro n
      simpa only [map_intCast] using
        congrArg (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p)) (h n)
    have hN : p*2 ≤ p*2*t := by simpa using Nat.mul_le_mul_left (p*2) ht
    have hb : (moll (p*2*t) : ZMod p) = 0 := by
      have he := noninert_zero hi 0 (p*2*t)
      rw [Nat.zero_add, pow_one, Nat.mul_one] at he
      exact he hN
    have h0 : (moll (p*2*t) : ZMod p) = moll 0 := by simpa using hsub.nat_mul (p*2) 0
    rw [hb] at h0
    simp [moll, gaussProd] at h0
  · rintro ⟨hP,hd⟩ n
    apply eq_of_components
    intro p e hp hq
    let : Fact p.Prime := ⟨hp⟩
    have hpm := (dvd_pow_self p (by omega : e+1 ≠ 0)).trans hq
    have hi := hP p (Nat.mem_primeFactors.mpr ⟨hp,hpm,hm.ne'⟩)
    exact (primePower_period_iff hi e).mpr
      ((eventual_iff hm).mp ((eventual_period_iff_dvd hm).mpr hd) p e hp hi hq) n

end MollRigidity
