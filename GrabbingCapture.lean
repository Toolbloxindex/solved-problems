module

public import GrabbingClaw
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace GraphGrabbing
open Finset

/-- Alice can play the remaining m rounds without Bob taking any target. -/
def Captures (E : Edge) (T : Vertices) : ℕ → Vertices → Prop
  | 0, _ => True
  | m+1, S => ∃ x, Legal E S x ∧ ∀ y, Legal E (S.erase x) y →
      y∉T ∧ Captures E T m ((S.erase x).erase y)

/-- A guaranteed margin in standard play, with both moves in each round
evaluated at the position where they are made. -/
def Wins (E : Edge) (w : ℕ → ℝ) : ℕ → Vertices → ℝ → Prop
  | 0, _, g => g≤0
  | m+1, S, g => ∃ x, Legal E S x ∧ ∀ y, Legal E (S.erase x) y →
      Wins E w m ((S.erase x).erase y) (g-w x+w y)

theorem capture_color {E : Edge} (sym : Undirected E) {col : ℕ → Bool}
    (bip : ∀ ⦃u v⦄, E u v → col u≠col v) (k : Bool) (T : Vertices)
    (same : ∀ x∈T, col x=k) (m : ℕ) (S : Vertices) (size : S.card=2*m)
    (conn : Connected E S) (free : ¬LongClaw E S)
    (unique : ∀ x∈T, Legal E S x → ∀ y∈T, Legal E S y → x=y) :
    Captures E T m S := by
  classical
  induction m generalizing S with
  | zero => trivial
  | succ m ih =>
    have opening : ∃ x, Legal E S x ∧ ∀ t∈T, ¬Legal E (S.erase x) t := by
      by_cases some : ∃ x∈T, Legal E S x
      · obtain ⟨x,xt,lx⟩ := some
        refine ⟨x,lx,?_⟩
        intro t tt after
        by_cases old : Legal E S t
        · exact (mem_erase.mp after.1).1 (unique t tt old x xt lx)
        · exact bip (exposes_edge sym conn lx.1 ⟨after,old⟩) ((same x xt).trans (same t tt).symm)
      · obtain ⟨x,lx,keep⟩ := safe_opening sym bip conn free k (by omega) ⟨m+1,by omega⟩
        refine ⟨x,lx,?_⟩
        intro t tt after
        exact keep t ⟨after,fun old => some ⟨t,tt,old⟩⟩ (same t tt)
    obtain ⟨x,lx,keep⟩ := opening
    refine ⟨x,lx,?_⟩
    intro y ly
    refine ⟨fun ht => keep y ht ly,ih _ ?_ ly.2 ?_ ?_⟩
    · rw [card_erase_of_mem ly.1,card_erase_of_mem lx.1]; omega
    · exact fun h => free (claw_mono ((erase_subset ..).trans (erase_subset ..)) h)
    · intro a ha la b hb lb
      exact exposes_unique sym (fun z e => bip e rfl) lx.2 ly.1
        ⟨la,keep a ha⟩ ⟨lb,keep b hb⟩

theorem wins_mono {E : Edge} {w : ℕ → ℝ} {m : ℕ} {S : Vertices} {a b : ℝ}
    (le : a≤b) (win : Wins E w m S b) : Wins E w m S a := by
  induction m generalizing S a b with
  | zero => exact le.trans win
  | succ m ih =>
    obtain ⟨x,lx,rest⟩ := win
    exact ⟨x,lx,fun y ly => ih (by linarith : a-w x+w y≤b-w x+w y) (rest y ly)⟩

private def tally (w : ℕ → ℝ) (T S : Vertices) := ∑ v∈S, if v∈T then w v else -w v

theorem capture_margin {E : Edge} {w : ℕ → ℝ} (nn : ∀ x,0≤w x)
    {T : Vertices} {m : ℕ} {S : Vertices} (size : S.card=2*m) (cap : Captures E T m S) :
    Wins E w m S (tally w T S) := by
  induction m generalizing S with
  | zero =>
    have eq : S=∅ := card_eq_zero.mp (by omega)
    simp [Wins,tally,eq]
  | succ m ih =>
    obtain ⟨x,lx,rest⟩ := cap
    refine ⟨x,lx,?_⟩
    intro y ly
    obtain ⟨out,sub⟩ := rest y ly
    apply wins_mono _ (ih (by rw [card_erase_of_mem ly.1,card_erase_of_mem lx.1];omega) sub)
    let f := fun v => if v∈T then w v else -w v
    have first := sum_erase_add S f lx.1
    have second := sum_erase_add (S.erase x) f ly.1
    have bx : f x≤w x := by dsimp [f]; split <;> linarith [nn x]
    have ey : f y= -w y := ite_eq_right out
    change (∑ v∈S,f v)-w x+w y ≤ ∑ v∈(S.erase x).erase y, f v
    linarith only [first,second,bx,ey]

/-- All nonnegative real weights are allowed provided adjacent positive
vertices carry equal weights. The number of positive vertices is unrestricted. -/
theorem win_equal_positive_edges {E : Edge} (sym : Undirected E) {col : ℕ → Bool}
    (bip : ∀ ⦃u v⦄, E u v → col u≠col v) (w : ℕ → ℝ) (nn : ∀ x,0≤w x)
    (m : ℕ) (S : Vertices) (size : S.card=2*m) (conn : Connected E S)
    (free : ¬InducedClaw E S)
    (equal : ∀ x∈S, ∀ y∈S, E x y → 0<w x → 0<w y → w x=w y) :
    Wins E w m S 0 := by
  classical
  have absent := fun h => free ((longClaw_iff_induced sym bip S).mp h)
  clear free
  induction m generalizing S with
  | zero => exact le_rfl
  | succ m ih =>
    by_cases available : ∃ x, Legal E S x ∧ 0<w x
    · let L := S.filter fun v => Legal E S v
      obtain ⟨z,lz,pz⟩ := available
      have zl : z∈L := mem_filter.mpr ⟨lz.1,lz⟩
      obtain ⟨x,xl,best⟩ := L.exists_max_image w ⟨z,zl⟩
      have lx := (mem_filter.mp xl).2
      have px := pz.trans_le (best z zl)
      refine ⟨x,lx,?_⟩
      intro y ly
      have ys := mem_of_mem_erase ly.1
      have affordable : w y≤w x := by
        by_contra! above
        have old : ¬Legal E S y := fun h => (not_lt_of_ge (best y (mem_filter.mpr ⟨ys,h⟩))) above
        exact above.ne (equal x lx.1 y ys (exposes_edge sym conn lx.1 ⟨ly,old⟩) px (px.trans above))
      have sub : ((S.erase x).erase y)⊆S := (erase_subset ..).trans (erase_subset ..)
      exact wins_mono (by linarith) (ih _ (by rw [card_erase_of_mem ly.1,card_erase_of_mem lx.1];omega)
        ly.2 (fun i hi j hj => equal i (sub hi) j (sub hj)) (fun h => absent (claw_mono sub h)))
    · let T := fun k : Bool => S.filter fun z => col z=k ∧ 0<w z
      have win (k : Bool) : Wins E w (m+1) S (tally w (T k) S) := by
        apply capture_margin nn size
        apply capture_color sym bip k _ (fun z hz => (mem_filter.mp hz).2.1) _ _ size conn absent
        intro x hx lx
        exact (available ⟨x,lx,(mem_filter.mp hx).2.2⟩).elim
      have zero : tally w (T true) S+tally w (T false) S=0 := by
        unfold tally
        rw [←sum_add_distrib]
        apply sum_eq_zero
        intro v vs
        by_cases pw : 0<w v
        · cases hv : col v <;> simp [T,vs,hv,pw]
        · have eq : w v=0 := le_antisymm (le_of_not_gt pw) (nn v)
          simp [eq]
      by_cases yes : 0≤tally w (T true) S
      · exact wins_mono yes (win true)
      · exact wins_mono (by linarith) (win false)

end GraphGrabbing
#print axioms GraphGrabbing.capture_color
#print axioms GraphGrabbing.win_equal_positive_edges
