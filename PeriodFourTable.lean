module

public import Window
public import Mathlib.Data.Fin.Basic

@[expose] public section

namespace KaylesRays.PeriodFour
open Positive
open Quartet (Mex)

/-- Rows indexed by host, minimum, and signed gap, with both leaf parities. -/
def rows : Nat → Nat → List Nat
  | 0, 0 => [4,7,7,4,4,7,7,4,4,7,11,4,4,6,10,8,6,7,10,5,6,7,10,5,6,7]
  | 0, 1 => [8,6,6,8,8,6,6,8,8,6,10,8,7,6,11,4,7,6,11,4,7,6,11,4,7,6]
  | 0, 2 => [10,7,7,4,9,7,7,4,9,7,11,4,6,7,10,5,6,7,10,5,6,7,10,5,6,7]
  | 0, 3 => [8,6,6,5,9,6,6,5,8,6,10,5,7,6,11,4,7,6,11,4,7,6,11,4,7,6]
  | 0, 4 => [8,7,7,4,9,7,7,4,8,7,11,4,6,7,10,5,6,7,10,5,6,7,10,5,6,7]
  | 0, 5 => [8,6,6,5,9,6,6,5,8,6,10,5,7,6,11,4,7,6,11,4,7,6,11,4,7,6]
  | 0, 6 => [8,7,7,4,9,7,7,4,8,7,11,4,6,7,10,5,6,7,10,5,6,7,10,5,6,7]
  | 1, 0 => [3,2,5,1,3,2,5,1,3,2,5,1,3,2,4,0,3,2,4,0,3,2,4,0,3,2]
  | 1, 1 => [2,3,4,0,2,3,4,0,2,3,4,0,2,3,5,1,2,3,5,1,2,3,5,1,2,3]
  | 1, 2 => [3,2,5,1,3,2,5,1,3,2,5,1,3,2,4,0,3,2,4,0,3,2,4,0,3,2]
  | 1, 3 => [2,3,4,0,2,3,4,0,2,3,4,0,2,3,5,1,2,3,5,1,2,3,5,1,2,3]
  | 1, 4 => [3,2,5,1,3,2,5,1,3,2,5,1,3,2,4,0,3,2,4,0,3,2,4,0,3,2]
  | 1, 5 => [2,3,4,0,2,3,4,0,2,3,4,0,2,3,5,1,2,3,5,1,2,3,5,1,2,3]
  | 1, 6 => [3,2,5,1,3,2,5,1,3,2,5,1,3,2,4,0,3,2,4,0,3,2,4,0,3,2]
  | 2, 0 => [1,5,2,3,1,5,2,3,1,5,2,3,1,5,3,2,1,5,3,2,1,5,3,2,1,5]
  | 2, 1 => [0,4,3,2,0,4,3,2,0,4,3,2,0,4,2,3,0,4,2,3,0,4,2,3,0,4]
  | 2, 2 => [1,5,2,3,1,5,2,3,1,5,2,3,1,5,3,2,1,5,3,2,1,5,3,2,1,5]
  | 2, 3 => [0,4,3,2,0,4,3,2,0,4,3,2,0,4,2,3,0,4,2,3,0,4,2,3,0,4]
  | 2, 4 => [1,5,2,3,1,5,2,3,1,5,2,3,1,5,3,2,1,5,3,2,1,5,3,2,1,5]
  | 2, 5 => [0,4,3,2,0,4,3,2,0,4,3,2,0,4,2,3,0,4,2,3,0,4,2,3,0,4]
  | 2, 6 => [1,5,2,3,1,5,2,3,1,5,2,3,1,5,3,2,1,5,3,2,1,5,3,2,1,5]
  | 3, 0 => [3,2,4,1,3,2,4,1,3,2,4,1,3,2,5,0,3,2,5,0,3,2,5,0,3,2]
  | 3, 1 => [2,3,5,0,2,3,5,0,2,3,5,0,2,3,4,1,2,3,4,1,2,3,4,1,2,3]
  | 3, 2 => [3,2,4,1,3,2,4,1,3,2,4,1,3,2,5,0,3,2,5,0,3,2,5,0,3,2]
  | 3, 3 => [2,3,5,0,2,3,5,0,2,3,5,0,2,3,4,1,2,3,4,1,2,3,4,1,2,3]
  | 3, 4 => [3,2,4,1,3,2,4,1,3,2,4,1,3,2,5,0,3,2,5,0,3,2,5,0,3,2]
  | 3, 5 => [2,3,5,0,2,3,5,0,2,3,5,0,2,3,4,1,2,3,4,1,2,3,4,1,2,3]
  | 3, 6 => [3,2,4,1,3,2,4,1,3,2,4,1,3,2,5,0,3,2,5,0,3,2,5,0,3,2]
  | 4, 0 => [3,1,3,1,3,1,3,1,3,1,3,1,3,1,2,5,4,1,2,3,4,1,2,3,4,1]
  | 4, 1 => [5,0,2,5,5,0,2,5,5,0,2,5,5,0,3,2,5,0,3,2,5,0,3,2,5,0]
  | 4, 2 => [4,1,3,2,4,1,3,2,4,1,3,2,4,1,2,3,4,1,2,3,4,1,2,3,4,1]
  | 4, 3 => [5,0,2,3,5,0,2,3,5,0,2,3,5,0,3,2,5,0,3,2,5,0,3,2,5,0]
  | 4, 4 => [4,1,3,2,4,1,3,2,4,1,3,2,4,1,2,3,4,1,2,3,4,1,2,3,4,1]
  | 4, 5 => [5,0,2,3,5,0,2,3,5,0,2,3,5,0,3,2,5,0,3,2,5,0,3,2,5,0]
  | 4, 6 => [4,1,3,2,4,1,3,2,4,1,3,2,4,1,2,3,4,1,2,3,4,1,2,3,4,1]
  | 5, 0 => [2,3,1,6,2,3,1,6,2,3,1,6,2,3,0,7,2,3,0,7,2,3,0,7,2,3]
  | 5, 1 => [3,2,0,7,3,2,0,7,3,2,0,7,3,2,1,6,3,2,1,6,3,2,1,6,3,2]
  | 5, 2 => [2,3,1,6,2,3,1,6,2,3,1,6,2,3,0,7,2,3,0,7,2,3,0,7,2,3]
  | 5, 3 => [3,2,0,7,3,2,0,7,3,2,0,7,3,2,1,6,3,2,1,6,3,2,1,6,3,2]
  | 5, 4 => [2,3,1,6,2,3,1,6,2,3,1,6,2,3,0,7,2,3,0,7,2,3,0,7,2,3]
  | 5, 5 => [3,2,0,7,3,2,0,7,3,2,0,7,3,2,1,6,3,2,1,6,3,2,1,6,3,2]
  | 5, 6 => [2,3,1,6,2,3,1,6,2,3,1,6,2,3,0,7,2,3,0,7,2,3,0,7,2,3]
  | 6, 0 => [3,2,9,1,3,2,9,1,3,2,9,1,3,2,8,0,3,2,8,0,3,2,8,0,3,2]
  | 6, 1 => [2,3,8,0,2,3,8,0,2,3,8,0,2,3,9,1,2,3,9,1,2,3,9,1,2,3]
  | 6, 2 => [3,2,9,1,3,2,9,1,3,2,9,1,3,2,8,0,3,2,8,0,3,2,8,0,3,2]
  | 6, 3 => [2,3,8,0,2,3,8,0,2,3,8,0,2,3,9,1,2,3,9,1,2,3,9,1,2,3]
  | 6, 4 => [3,2,9,1,3,2,9,1,3,2,9,1,3,2,8,0,3,2,8,0,3,2,8,0,3,2]
  | 6, 5 => [2,3,8,0,2,3,8,0,2,3,8,0,2,3,9,1,2,3,9,1,2,3,9,1,2,3]
  | 6, 6 => [3,2,9,1,3,2,9,1,3,2,9,1,3,2,8,0,3,2,8,0,3,2,8,0,3,2]
  | 7, 0 => [3,2,8,1,3,2,8,1,3,2,8,1,3,2,9,0,3,2,9,0,3,2,9,0,3,2]
  | 7, 1 => [2,3,9,0,2,3,9,0,2,3,9,0,2,3,8,1,2,3,8,1,2,3,8,1,2,3]
  | 7, 2 => [3,2,8,1,3,2,8,1,3,2,8,1,3,2,9,0,3,2,9,0,3,2,9,0,3,2]
  | 7, 3 => [2,3,9,0,2,3,9,0,2,3,9,0,2,3,8,1,2,3,8,1,2,3,8,1,2,3]
  | 7, 4 => [3,2,8,1,3,2,8,1,3,2,8,1,3,2,9,0,3,2,9,0,3,2,9,0,3,2]
  | 7, 5 => [2,3,9,0,2,3,9,0,2,3,9,0,2,3,8,1,2,3,8,1,2,3,8,1,2,3]
  | 7, 6 => [3,2,8,1,3,2,8,1,3,2,8,1,3,2,9,0,3,2,9,0,3,2,9,0,3,2]
  | _, _ => []
def masks : List Nat := [15,7,45,71,132,227,247,1271]
def erased : List Nat := [4,3,1,3,0,2,3,3]

def raw (h : Nat) (x c : Int) (z : Bool) : Nat :=
  (rows h (min x c).toNat)[2*(c-x+6).toNat+z.toNat]?.getD 0

def profile (h : Nat) : Int → Int → Bool → Nat :=
  lifted (raw h)

def exits (quiet : Nat → Int → Int → Bool → Nat) (h : Nat) (x c : Int) (z : Bool) : List Nat :=
  let p := (x%2).toNat
  let q := (c%2).toNat
  let d := (3*p) ^^^ (2*q) ^^^ z.toNat
  let a := erased[h]?.getD 0
  let mask := masks[h]?.getD 0
  (List.range 12 |>.filter (fun k => mask.testBit k) |>.map (· ^^^ d)) ++
    [q ^^^ (if h=0 then 1 else 0), a ^^^ d ^^^ 1] ++
    (if 0<c then [a ^^^ d ^^^ 3] else []) ++
    (if h=0 then (List.range 7).map (fun i => quiet (i+1) x c z) else [])

def isMex (l : List Nat) (v : Nat) : Bool :=
  (decide (v ∉ l)) && (List.range v).all (fun k => decide (k ∈ l))

private theorem ofCheck {l : List Nat} {v : Nat} (h : isMex l v = true) :
    Mex (· ∈ l) v := by
  simp only [isMex, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact h

def cell (h m d : Nat) (z : Bool) : Bool :=
  let p := coordinates m ((d : Int)-8)
  isMex (options (exits profile h) (profile h) p.1 p.2 z) (profile h p.1 p.2 z)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem allCells : ∀ (h m : Fin 8) (d : Fin 17) (z : Bool),
    cell h.val m.val d.val z = true := by
  suffices rows : ∀ (h m : Nat), h<8 → m<8 → ∀ (d : Fin 17) (z : Bool),
      cell h m d.val z = true by
    intro h m
    exact rows h.val m.val h.isLt m.isLt
  intro h m hh hm
  have a : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 := by omega
  have b : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 ∨ m=6 ∨ m=7 := by omega
  rcases a with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases b with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

private theorem inWindow (h : Nat) (hh : h<8) :
    ∀ m d z, 0≤m → m<8 → -8≤d → d≤8 →
      let p := coordinates m d
      Mex (· ∈ options (exits profile h) (profile h) p.1 p.2 z) (profile h p.1 p.2 z) := by
  intro m d z hm hm' hd hd'
  let i : Fin 8 := ⟨m.toNat,by omega⟩
  let j : Fin 17 := ⟨(d+8).toNat,by omega⟩
  have a : (i.val : Int) = m := by dsimp [i]; omega
  have b : (j.val : Int)-8 = d := by dsimp [j]; omega
  have test := ofCheck (allCells ⟨h,hh⟩ i j z)
  simp only [a,b] at test
  exact test

private theorem commute (h : Nat) (x c : Int) (z : Bool) (hx : 0≤x) (hc : 0≤c) :
    let p := representative 4 5 x c
    exits profile h x c z = exits profile h p.1 p.2 z := by
  let p := representative 4 5 x c
  obtain ⟨_,_,_,g,r,s⟩ := detailed x c hx hc
  have same (i : Nat) : profile (i+1) x c z = profile (i+1) p.1 p.2 z := by
    have e := transport 3 3 x c 0 0 (by decide) (by decide) (by decide)
    simp only [Int.add_zero] at e
    change representative 3 3 p.1 p.2 = representative 3 3 x c at e
    simpa only [profile,lifted] using (congrArg (fun t : Int × Int => raw (i+1) t.1 t.2 z) e).symm
  change exits profile h x c z = exits profile h p.1 p.2 z
  unfold exits
  simp only [show x%2=p.1%2 by exact r.symm,show c%2=p.2%2 by exact s.symm,
    show (0<c ↔ 0<p.2) by exact g,same]

theorem profile_mex (h : Nat) (hh : h<8) (x c : Int) (z : Bool) (hx : 0≤x) (hc : 0≤c) :
    Mex (· ∈ options (exits profile h) (profile h) x c z) (profile h x c z) :=
  window (exits profile h) (raw h) (commute h) (inWindow h hh) x c z hx hc

/-- The eight coupled mex equations determine the values in every board size. -/
theorem fixed_profile (f : Nat → Int → Int → Bool → Nat)
    (rule : ∀ h<8, ∀ x c z, 0≤x → 0≤c →
      Mex (· ∈ options (exits f h) (f h) x c z) (f h x c z)) :
    ∀ h<8, ∀ x c z, 0≤x → 0≤c → f h x c z = profile h x c z := by
  have children : ∀ h<8, 0<h → ∀ x c z, 0≤x → 0≤c → f h x c z = profile h x c z := by
    intro h hh hp
    have e : exits f h = exits profile h := by
      funext x c z
      simp [exits,show h≠0 by omega]
    apply determined (exits profile h) (f h) (profile h) _ (profile_mex h hh)
    intro x c z hx hc
    simpa only [e] using rule h hh x c z hx hc
  intro h hh
  by_cases hp : 0<h
  · exact children h hh hp
  have zero : h=0 := by omega
  subst h
  have same (x c : Int) (z : Bool) (hx : 0≤x) (hc : 0≤c) :
      exits f 0 x c z = exits profile 0 x c z := by
    simp only [exits,ite_true]
    congr 1
    apply List.map_congr_left
    intro i hi
    have q : i<7 := List.mem_range.mp hi
    exact children (i+1) (by omega) (by omega) x c z hx hc
  apply determined (exits profile 0) (f 0) (profile 0) _ (profile_mex 0 (by decide))
  intro x c z hx hc
  have h := rule 0 (by decide) x c z hx hc
  unfold options at h ⊢
  simpa only [same x c z hx hc] using h

private theorem pattern (j : Nat) :
    profile 0 (4*(j : Int)+5) 3 false = 8 ∧ profile 0 (4*(j : Int)+7) 3 false = 9 := by
  constructor
  · by_cases h : j=0
    · subst j
      decide
    · have e : representative 3 3 (4*(j : Int)+5) 3 = (9,3) := by
        unfold representative coordinates
        rw [Int.min_eq_right (by omega)]
        rw [signedCap,ite_eq_left (by omega)]
        have z : cap 3 (-(3-(4*(j : Int)+5)))=6 := by unfold cap; split <;> omega
        rw [z]
        decide
      simp only [profile,lifted,e]
      decide
  · have e : representative 3 3 (4*(j : Int)+7) 3 = (7,3) := by
      unfold representative coordinates
      rw [Int.min_eq_right (by omega)]
      rw [signedCap,ite_eq_left (by omega)]
      have z : cap 3 (-(3-(4*(j : Int)+7)))=4 := by unfold cap; split <;> omega
      rw [z]
      decide
    simp only [profile,lifted,e]
    decide

/-- The recurrent values differ at arbitrarily late indices two apart.
The hypothesis still needs to be discharged on the literal host. -/
theorem witness_recurrence (f : Nat → Int → Int → Bool → Nat)
    (rule : ∀ h<8, ∀ x c z, 0≤x → 0≤c →
      Mex (· ∈ options (exits f h) (f h) x c z) (f h x c z)) (j : Nat) :
    f 0 (4*(j : Int)+5) 3 false = 8 ∧ f 0 (4*(j : Int)+7) 3 false = 9 := by
  rw [fixed_profile f rule 0 (by decide) _ _ _ (by omega) (by decide),
    fixed_profile f rule 0 (by decide) _ _ _ (by omega) (by decide)]
  exact pattern j

#print axioms KaylesRays.PeriodFour.witness_recurrence

end KaylesRays.PeriodFour
