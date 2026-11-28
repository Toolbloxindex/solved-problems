module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push
public import MollRigidity
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace ArctanPole
open Finset

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

omit [UniqueFactorizationMonoid R] in
private theorem remove_max {ι : Type*} [DecidableEq ι] {I : Finset ι} (hi : I.Nonempty)
    {p : R} (hp : Prime p) (a : ι → R) {F : R}
    (hF : ∀ j ∈ I, (∏ k ∈ I.erase j, (a k-a j)) ∣ F) :
    ∃ j ∈ I, emultiplicity p (∏ k ∈ I, a k) ≤ emultiplicity p F + emultiplicity p (a j) := by
  obtain ⟨j, hj, hmax⟩ := I.exists_max_image (fun k => emultiplicity p (a k)) hi
  refine ⟨j, hj, ?_⟩
  have hkj (k : ι) (hk : k ∈ I.erase j) :
      emultiplicity p (a k) ≤ emultiplicity p (a k-a j) := by
    have hle := hmax k (mem_of_mem_erase hk)
    have hh := min_le_emultiplicity_add (p := p) (a := a k) (b := -a j)
    simpa only [emultiplicity_neg, min_eq_left hle, sub_eq_add_neg] using hh
  have hu : emultiplicity p (∏ k ∈ I.erase j, a k) ≤ emultiplicity p F := by
    apply le_trans _ (emultiplicity_le_emultiplicity_of_dvd_right (hF j hj))
    rw [Finset.emultiplicity_prod hp, Finset.emultiplicity_prod hp]
    exact sum_le_sum hkj
  rw [← mul_prod_erase I a hj, emultiplicity_mul hp, add_comm]
  exact add_le_add hu (le_refl _)

/-- Bound a common divisor of two products using the differences within each list and
the sums between lists. The estimate includes primes dividing several of the factors. -/
theorem two_products_dvd {ι : Type*} [DecidableEq ι] {I : Finset ι} (hi : I.Nonempty)
    {a b : ι → R} {g F L : R} (hg : g ≠ 0)
    (ha : g ∣ ∏ k ∈ I, a k) (hb : g ∣ ∏ k ∈ I, b k)
    (hFa : ∀ j ∈ I, (∏ k ∈ I.erase j, (a k-a j)) ∣ F)
    (hFb : ∀ j ∈ I, (∏ k ∈ I.erase j, (b k-b j)) ∣ F)
    (hL : ∀ j ∈ I, ∀ k ∈ I, a j+b k ∣ L) : g ∣ F*L := by
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hg).mpr
  intro p hp
  obtain ⟨j,hj,H⟩ := remove_max hi hp a hFa
  obtain ⟨k,hk,H'⟩ := remove_max hi hp b hFb
  have hmin := (min_le_emultiplicity_add (p := p) (a := a j) (b := b k)).trans
    (emultiplicity_le_emultiplicity_of_dvd_right (hL j hj k hk))
  rw [emultiplicity_mul hp]
  rcases le_total (emultiplicity p (a j)) (emultiplicity p (b k)) with h|h
  · rw [min_eq_left h] at hmin
    exact ((emultiplicity_le_emultiplicity_of_dvd_right ha).trans H).trans (add_le_add (le_refl _) hmin)
  · rw [min_eq_right h] at hmin
    exact ((emultiplicity_le_emultiplicity_of_dvd_right hb).trans H').trans (add_le_add (le_refl _) hmin)

#print axioms two_products_dvd

end ArctanPole

namespace ArctanPole
open Finset

/-- The product of the differences from one integer in an interval, with that
integer omitted, divides the factorial of the interval's diameter. -/
theorem factorial_diffs {R : Type*} [CommRing R] (n j : ℕ) (hj : j ∈ range n) :
    (∏ k ∈ (range n).erase j, ((k:R)-(j:R))) ∣ ((n-1).factorial:R) := by
  have hjn := mem_range.mp hj
  have he : (range n).erase j = range j ∪ Ico (j+1) n := by
    ext k
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hd : Disjoint (range j) (Ico (j+1) n) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨ha,_⟩ := mem_Ico.mp hk'
    have := mem_range.mp hk
    omega
  have hleft : (∏ k ∈ range j, ((k:R)-j)) = (-1:R)^j * j.factorial := by
    calc
      _ = ∏ k ∈ range j, (-1:R)*((j:R)-k) := by
        apply prod_congr rfl
        intro k _
        ring
      _ = _ := by rw [prod_mul_distrib,prod_const, card_range,prod_range_natCast_sub,
                        ←Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  have hright : (∏ k ∈ Ico (j+1) n, ((k:R)-j)) = ((n-1-j).factorial:R) := by
    rw [prod_Ico_eq_prod_range]
    have hn : n-(j+1)=n-1-j := by omega
    rw [hn,Nat.factorial_eq_prod_range_add_one,prod_natCast]
    apply prod_congr rfl
    intro k _
    push_cast
    ring
  rw [he,prod_union hd,hleft,hright]
  have hchoose := Nat.choose_mul_factorial_mul_factorial (n:=n-1) (k:=j) (by omega)
  refine ⟨(-1:R)^j * ((n-1).choose j:R), ?_⟩
  have hu : (-1:R)^j * (-1:R)^j = 1 := by rw [←mul_pow]; simp
  calc
    _ = (((n-1).choose j:R)*j.factorial)*(n-1-j).factorial := by
      simpa only [Nat.cast_mul] using congrArg (fun z : ℕ => (z:R)) hchoose.symm
    _ = _ := by linear_combination -(((n-1).choose j:R)*j.factorial*(n-1-j).factorial)*hu

#print axioms factorial_diffs

end ArctanPole

namespace ArctanPole
open Finset MollRigidity

def gaussianI : GaussianInt := ⟨0, 1⟩

private theorem shifted_products (n : ℕ) :
    (∏ k ∈ range n, ((k:GaussianInt) + 1 - gaussianI)) =
      (-gaussianI)^n * gaussProd n ∧
    (∏ k ∈ range n, ((k:GaussianInt) + 1 + gaussianI)) =
      gaussianI^n * star (gaussProd n) := by
  induction n with
  | zero => simp [gaussProd]
  | succ n ih =>
    have hprod : gaussProd (n+1) = gaussProd n * ⟨1, ((n+1:ℕ):ℤ)⟩ :=
      prod_Icc_succ_top (by omega) _
    have h₁ : (n:GaussianInt)+1-gaussianI =
        (-gaussianI)*(⟨1,((n+1:ℕ):ℤ)⟩ : GaussianInt) := by
      ext <;> simp [gaussianI, Zsqrtd.re_mul, Zsqrtd.im_mul]
    have h₂ : (n:GaussianInt)+1+gaussianI =
        gaussianI * star (⟨1,((n+1:ℕ):ℤ)⟩ : GaussianInt) := by
      ext <;> simp [gaussianI, Zsqrtd.re_mul, Zsqrtd.im_mul]
    simp only [prod_range_succ, ih.1, ih.2, h₁, h₂, hprod, star_mul, pow_succ]
    constructor <;> ac_rfl

private theorem gaussProd_ne_zero (n : ℕ) : gaussProd n ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro k _ hz
  have h := congrArg Zsqrtd.re hz
  exact (one_ne_zero : (1:ℤ) ≠ 0) h

/-- The positive coordinate gcd of the original product divides the interval factorial
times the least common multiple of all positive integers through twice the index. -/
theorem gaussian_content (n : ℕ) (hn : 0 < n) :
    Int.gcd (gaussProd n).re (gaussProd n).im ∣
      (n-1).factorial * ((Icc 1 (2*n)).lcm id) := by
  let g := Int.gcd (gaussProd n).re (gaussProd n).im
  have hgr : (g:ℤ) ∣ (gaussProd n).re := Int.gcd_dvd_left ..
  have hgi : (g:ℤ) ∣ (gaussProd n).im := Int.gcd_dvd_right ..
  have hd : (g:GaussianInt) ∣ gaussProd n := by
    simpa only [Int.cast_natCast] using (Zsqrtd.intCast_dvd (g:ℤ) _).mpr ⟨hgr,hgi⟩
  have hd' : (g:GaussianInt) ∣ star (gaussProd n) := by
    simpa only [Int.cast_natCast] using (Zsqrtd.intCast_dvd (g:ℤ) (star (gaussProd n))).mpr
      ⟨hgr, by simpa only [Zsqrtd.im_star, dvd_neg] using hgi⟩
  have hg : (g:GaussianInt) ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hd
    exact gaussProd_ne_zero n hd
  let a (k : ℕ) := (k:GaussianInt)+1-gaussianI
  let b (k : ℕ) := (k:GaussianInt)+1+gaussianI
  have ha : (g:GaussianInt) ∣ ∏ k ∈ range n, a k := by
    rw [show (∏ k ∈ range n, a k) = _ from (shifted_products n).1]
    exact dvd_mul_of_dvd_right hd _
  have hb : (g:GaussianInt) ∣ ∏ k ∈ range n, b k := by
    rw [show (∏ k ∈ range n, b k) = _ from (shifted_products n).2]
    exact dvd_mul_of_dvd_right hd' _
  let L := (Icc 1 (2*n)).lcm id
  have hG : (g:GaussianInt) ∣ ((n-1).factorial:GaussianInt) * (L:GaussianInt) := by
    apply two_products_dvd (nonempty_range_iff.mpr hn.ne') hg ha hb
    · intro j hj
      simpa only [a, sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] using factorial_diffs (R := GaussianInt) n j hj
    · intro j hj
      simpa only [b, add_sub_add_right_eq_sub] using factorial_diffs (R := GaussianInt) n j hj
    · intro j hj k hk
      have hj' := mem_range.mp hj
      have hk' := mem_range.mp hk
      have he : a j + b k = ((j+k+2:ℕ):GaussianInt) := by
        dsimp [a,b]; push_cast; ring
      rw [he]
      have hNat : j+k+2 ∣ L := Finset.dvd_lcm (f:=id) (mem_Icc.mpr ⟨by omega, by omega⟩)
      obtain ⟨z,hz⟩ := hNat
      exact ⟨z, by rw [hz, Nat.cast_mul]⟩
  apply Int.natCast_dvd_natCast.mp
  apply (Zsqrtd.intCast_dvd_intCast (d := -1) _ _).mp
  simpa only [Int.cast_natCast, Int.cast_mul, Nat.cast_mul] using hG

#print axioms gaussian_content
end ArctanPole
