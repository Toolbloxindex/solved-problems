import Lean.Elab.Tactic.Omega

namespace KaylesRays.Quartet

/-- Four stands for a value outside the current block. -/
def digit (b n : Nat) : Nat := if n/4=b then n%4 else 4

def live (b n : Nat) : Prop := 4*b ≤ n

def Mex (P : Nat → Prop) (m : Nat) := (¬P m) ∧ ∀ k<m, P k

/-- The four bits of a single block, with the first hole or sentinel four. -/
def Hole (P : Nat → Prop) (h : Nat) : Prop :=
  h ≤ 4 ∧ (h<4 → ¬P h) ∧ ∀ k<h, P k

theorem unique {P a b} (ha : Hole P a) (hb : Hole P b) : a=b := by
  have := ha.1
  have := hb.1
  by_cases h : a<b
  · exact False.elim (ha.2.1 (by omega) (hb.2.2 a h))
  · by_cases j : b<a
    · exact False.elim (hb.2.1 (by omega) (ha.2.2 b j))
    · omega

theorem digit_eq {b n k : Nat} (hk : k<4) :
    digit b n = k ↔ n=4*b+k := by
  unfold digit
  split <;> omega

theorem digit_hole {P m} (h : Mex P m) {b} (active : live b m) :
    Hole (fun k => P (4*b+k)) (digit b m) := by
  unfold live at active
  unfold digit Hole
  split <;> rename_i eq
  · refine ⟨by omega,fun _ hn => h.1 ?_,fun k hk => h.2 _ (by omega)⟩
    change P (4*b+m%4) at hn
    rwa [show 4*b+m%4=m by omega] at hn
  · exact ⟨by omega,by omega,fun k hk => h.2 _ (by omega)⟩

theorem next_live (b n : Nat) :
    live (b+1) n ↔ live b n ∧ digit b n=4 := by
  unfold live digit
  split <;> omega

/-- Every shifted wire can be evaluated using only the four current bits. -/
theorem shifted_wire {b n d k : Nat} (hd : d<4) (hk : k<4) :
    (n ^^^ d = 4*b+k) ↔ digit b n = (k ^^^ d) := by
  have low : k ^^^ d < 4 := Nat.xor_lt_two_pow (x := k) (y := d) (n := 2) hk hd
  rw [digit_eq low]
  have shift : (4*b+k) ^^^ d = 4*b+(k ^^^ d) := by
    have quot : ((4*b+k) ^^^ d)/2^2 = (4*b+k)/2^2 ^^^ d/2^2 := Nat.xor_div_two_pow
    have remn : ((4*b+k) ^^^ d)%2^2 = (4*b+k)%2^2 ^^^ d%2^2 := Nat.xor_mod_two_pow
    change ((4*b+k) ^^^ d)/4 = (4*b+k)/4 ^^^ d/4 at quot
    change ((4*b+k) ^^^ d)%4 = (4*b+k)%4 ^^^ d%4 at remn
    rw [Nat.div_eq_of_lt hd,Nat.xor_zero] at quot
    rw [Nat.mod_eq_of_lt hd,show (4*b+k)%4=k by omega] at remn
    omega
  rw [←shift]
  constructor <;> intro e <;> simpa [Nat.xor_assoc] using congrArg (· ^^^ d) e

/-- A finite verifier can compare any pair of mex wires block by block.
`step` is its checked reachable-state invariant. Its input digits and arithmetic
for individual wires are supplied by `digit_hole` and `shifted_wire`. -/
theorem eq_of_invariant {I : Type} (v : I → Nat) (a c : I)
    (Inv : (I → Prop) → Prop)
    (start : Inv (fun i => live 0 (v i)))
    (step : ∀ b, Inv (fun i => live b (v i)) →
      digit b (v a) = digit b (v c) ∧ Inv (fun i => live (b+1) (v i))) :
    v a = v c := by
  have reach : ∀ b, Inv (fun i => live b (v i)) := by
    intro b
    induction b with
    | zero => exact start
    | succ b ih => exact (step b ih).2
  let b := v a / 4
  have eq := (step b (reach b)).1
  have low : v a % 4 < 4 := by omega
  have aa : digit b (v a) = v a%4 := (digit_eq low).mpr (by dsimp [b]; omega)
  have cc := (digit_eq low).mp (eq.symm.trans aa)
  dsimp [b] at cc
  omega

end KaylesRays.Quartet
#print axioms KaylesRays.Quartet.shifted_wire
#print axioms KaylesRays.Quartet.eq_of_invariant

namespace KaylesRays.Positive

open KaylesRays.Quartet (Mex)

def cap (b n : Int) : Int := if n<b then n else b+(n-b)%4

def signedCap (b d : Int) : Int := if d<0 then -(cap b (-d)) else cap b d

private theorem cap_move (b r n step : Int) (hs : -r≤step) :
    cap b (cap (b+r) n+step) = cap b (n+step) := by
  by_cases hn : n<b+r
  · simp [cap,hn]
  · have test : ¬b+r+(n-(b+r))%4+step<b := by omega
    have full : ¬n+step<b := by omega
    simp only [cap,ite_eq_right hn,ite_eq_right test,ite_eq_right full]
    omega

private theorem pair_move (b h m d u v : Int) (hh : 0≤h) (hd : 0≤d)
    (hu : -1≤u ∧ u≤1) (hv : -1≤v ∧ v≤1) :
    let M := cap (b+1) m
    let D := cap (h+2) d
    (cap b (min (M+u) (M+D+v)), signedCap h (D+v-u)) =
      (cap b (min (m+u) (m+d+v)), signedCap h (d+v-u)) := by
  dsimp only
  have offset : min u (cap (h+2) d+v)=min u (d+v) := by
    by_cases near : d<h+2
    · simp [cap,near]
    · simp only [cap,ite_eq_right near]
      omega
  have shift : ∀ a c : Int, min (a+u) (a+c+v) = a+min u (c+v) := by
    intros
    omega
  apply Prod.ext
  · simp only [shift,offset]
    exact cap_move b 1 m (min u (d+v)) (by omega)
  · by_cases near : d<h+2
    · simp [cap,near]
    · have safe : 0 ≤ cap (h+2) d+v-u := by simp only [cap,ite_eq_right near]; omega
      have safe' : 0 ≤ d+v-u := by omega
      simp only [signedCap,ite_eq_right (show ¬cap (h+2) d+v-u<0 by omega),
        ite_eq_right (show ¬d+v-u<0 by omega)]
      have eq := cap_move h 2 d (v-u) (by omega)
      simpa only [Int.add_sub_assoc] using eq

def coordinates (m d : Int) : Int × Int := (m + max 0 (-d), m + max 0 d)

/-- The first cap is on the minimum and the second on the signed gap. -/
def representative (b h x c : Int) : Int × Int :=
  coordinates (cap b (min x c)) (signedCap h (c-x))

private theorem signedCap_neg (h d : Int) (hh : 0 ≤ h) :
    signedCap h (-d) = -signedCap h d := by
  by_cases lt : d < 0
  · rw [signedCap, signedCap, ite_eq_right (show ¬-d < 0 by omega), ite_eq_left lt]
    omega
  · by_cases gt : 0 < d
    · rw [signedCap, signedCap, ite_eq_left (show -d < 0 by omega), ite_eq_right lt,
        Int.neg_neg]
    · have eq : d = 0 := by omega
      have cz : cap h 0 = 0 := by
        by_cases hp : 0 < h
        · simp [cap, hp]
        · have : h = 0 := by omega
          simp [cap, this]
      simp [signedCap, eq, cz]

theorem transport (b h x c u v : Int) (hh : 0 ≤ h)
    (hu : -1 ≤ u ∧ u ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1) :
    let d := representative (b+1) (h+2) x c
    representative b h (d.1+u) (d.2+v) = representative b h (x+u) (c+v) := by
  have nonneg (t n : Int) (ht : 0 ≤ t) (hn : 0 ≤ n) : 0 ≤ cap t n := by
    unfold cap
    split <;> omega
  by_cases cmp : x ≤ c
  · have large : 0 ≤ cap (h+2) (c-x) := nonneg _ _ (by omega) (by omega)
    have swap : x+(c-x) = c := by omega
    have p := pair_move b h x (c-x) u v hh (by omega) hu hv
    dsimp only at p
    rw [swap] at p
    have rep : representative (b+1) (h+2) x c =
        (cap (b+1) x, cap (b+1) x + cap (h+2) (c-x)) := by
      rw [representative, Int.min_eq_left cmp, signedCap, ite_eq_right (show ¬c-x<0 by omega)]
      unfold coordinates
      congr 1 <;> omega
    rw [rep]
    dsimp only
    unfold representative
    rw [show cap (b+1) x + cap (h+2) (c-x) + v - (cap (b+1) x + u) =
      cap (h+2) (c-x)+v-u by omega, show c+v-(x+u) = c-x+v-u by omega]
    exact congrArg (fun r : Int × Int => coordinates r.1 r.2) p
  · have large : 0 ≤ cap (h+2) (x-c) := nonneg _ _ (by omega) (by omega)
    have swap : c+(x-c) = x := by omega
    have p := pair_move b h c (x-c) v u hh (by omega) hv hu
    dsimp only at p
    rw [swap] at p
    have rep : representative (b+1) (h+2) x c =
        (cap (b+1) c + cap (h+2) (x-c), cap (b+1) c) := by
      rw [representative, Int.min_eq_right (by omega), signedCap,
        ite_eq_left (by omega), show -(c-x)=x-c by omega]
      unfold coordinates
      congr 1 <;> omega
    rw [rep]
    dsimp only
    unfold representative
    have sg₁ : cap (b+1) c + v - (cap (b+1) c + cap (h+2) (x-c) + u) =
        -(cap (h+2) (x-c)+u-v) := by omega
    have sg₂ : c+v-(x+u) = -(x-c+u-v) := by omega
    rw [sg₁, sg₂, signedCap_neg _ _ hh, signedCap_neg _ _ hh,
      Int.min_comm (cap (b+1) c + cap (h+2) (x-c) + u), Int.min_comm (x+u)]
    exact congrArg (fun r : Int × Int => coordinates r.1 (-r.2)) p

/-- On a board with at least one leaf, the two-edge arms factor out.
The five interior move values that remain are listed here. -/
def options (ext : Int → Int → Bool → List Nat) (f : Int → Int → Bool → Nat)
    (x c : Int) (z : Bool) : List Nat :=
  ext x c z ++
    (if 0 < x then [f (x-1) c false ^^^ 1, f (x-1) c true ^^^ 1,
      f (x-1) (c+1) z] else []) ++
    (if 0 < c then [f x (c-1) false, f x (c-1) true] else [])

theorem unique {P : Nat → Prop} {a b : Nat} (ha : Mex P a) (hb : Mex P b) : a = b := by
  have an : ¬a < b := fun h => ha.1 (hb.2 a h)
  have bn : ¬b < a := fun h => hb.1 (ha.2 b h)
  omega

theorem determined (ext : Int → Int → Bool → List Nat) (f g : Int → Int → Bool → Nat)
    (hf : ∀ x c z, 0 ≤ x → 0 ≤ c → Mex (· ∈ options ext f x c z) (f x c z))
    (hg : ∀ x c z, 0 ≤ x → 0 ≤ c → Mex (· ∈ options ext g x c z) (g x c z)) :
    ∀ x c z, 0 ≤ x → 0 ≤ c → f x c z = g x c z := by
  suffices go : ∀ n : Nat, ∀ x c z, 0 ≤ x → 0 ≤ c → (2*x+c).toNat = n →
      f x c z = g x c z from fun x c z hx hc => go _ x c z hx hc rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x c z hx hc rank
    have atFive (px : 0 < x) (t : Bool) :
        f (x-1) c t = g (x-1) c t := ih _ (by omega) _ _ _ (by omega) hc rfl
    have atTip (px : 0 < x) :
        f (x-1) (c+1) z = g (x-1) (c+1) z := ih _ (by omega) _ _ _ (by omega) (by omega) rfl
    have atThree (pc : 0 < c) (t : Bool) :
        f x (c-1) t = g x (c-1) t := ih _ (by omega) _ _ _ hx (by omega) rfl
    have eq : options ext f x c z = options ext g x c z := by
      by_cases px : 0 < x <;> by_cases pc : 0 < c <;>
        simp [options, px, pc, atFive, atTip, atThree]
    apply unique (hf x c z hx hc)
    simpa [eq] using hg x c z hx hc

def lifted (raw : Int → Int → Bool → Nat) (x c : Int) (z : Bool) : Nat :=
  let p := representative 3 3 x c
  raw p.1 p.2 z

theorem detailed (x c : Int) (hx : 0≤x) (hc : 0≤c) :
    let m := cap 4 (min x c)
    let d := signedCap 5 (c-x)
    let p := representative 4 5 x c
    (0≤m ∧ m<8) ∧ (-8≤d ∧ d≤8) ∧
      (0<x ↔ 0<p.1) ∧ (0<c ↔ 0<p.2) ∧ p.1%2=x%2 ∧ p.2%2=c%2 := by
  have cap_info (b n : Int) (hb : 1≤b) (hn : 0≤n) :
      (0≤cap b n ∧ cap b n≤b+3) ∧
        (0<n ↔ 0<cap b n) ∧ (cap b n)%2=n%2 := by
    unfold cap
    split <;> omega
  have hm := cap_info 4 (min x c) (by omega) (by omega)
  by_cases cmp : x≤c
  · have hg := cap_info 5 (c-x) (by omega) (by omega)
    simp only [representative, coordinates, Int.min_eq_left cmp, signedCap,
      ite_eq_right (show ¬c-x<0 by omega)] at *
    omega
  · have hg := cap_info 5 (x-c) (by omega) (by omega)
    simp only [representative, coordinates, Int.min_eq_right (show c≤x by omega), signedCap,
      ite_eq_left (show c-x<0 by omega), show -(c-x)=x-c by omega] at *
    omega

theorem window (ext : Int → Int → Bool → List Nat) (raw : Int → Int → Bool → Nat)
    (external : ∀ x c z, 0≤x → 0≤c →
      let p := representative 4 5 x c
      ext x c z = ext p.1 p.2 z)
    (finite : ∀ m d z, 0≤m → m<8 → -8≤d → d≤8 →
      let p := coordinates m d
      Mex (· ∈ options ext (lifted raw) p.1 p.2 z) (lifted raw p.1 p.2 z)) :
    ∀ x c z, 0≤x → 0≤c →
      Mex (· ∈ options ext (lifted raw) x c z) (lifted raw x c z) := by
  intro x c z hx hc
  let p := representative 4 5 x c
  have info := detailed x c hx hc
  obtain ⟨⟨hm,hm'⟩,⟨hd,hd'⟩,ex,ec,_,_⟩ := info
  have lift (u v : Int) (hu : -1≤u ∧ u≤1) (hv : -1≤v ∧ v≤1) (s : Bool) :
      lifted raw (p.1+u) (p.2+v) s = lifted raw (x+u) (c+v) s := by
    unfold lifted
    exact congrArg (fun q : Int × Int => raw q.1 q.2 s) (transport 3 3 x c u v (by decide) hu hv)
  have lf := lift (-1) 0 (by decide) (by decide)
  have lt := lift (-1) 1 (by decide) (by decide)
  have lc := lift 0 (-1) (by decide) (by decide)
  have self := lift 0 0 (by decide) (by decide) z
  simp only [Int.add_zero, Int.add_neg_eq_sub] at lf lt lc self
  have opts : options ext (lifted raw) x c z = options ext (lifted raw) p.1 p.2 z := by
    unfold options
    rw [external x c z hx hc, ←lf, ←lf, ←lt, ←lc, ←lc]
    simp only [ex,ec,p]
  rw [opts, ←self]
  exact finite _ _ _ hm hm' hd hd'

end KaylesRays.Positive

#print axioms KaylesRays.Positive.transport
#print axioms KaylesRays.Positive.determined
#print axioms KaylesRays.Positive.window
