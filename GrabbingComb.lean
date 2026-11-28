module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace GraphGrabbing.Comb
open Finset

/-- The hubs of the remaining rooted path are 0,...,h−1, with 0 the root.
A leaf is indexed by its parent. -/
inductive Token where
  | hub (i : ℕ)
  | leaf (i : ℕ)
deriving DecidableEq

inductive Move : ℕ → Finset ℕ → Token → ℕ → Finset ℕ → Prop where
  | hub {i L} (free : i ∉ L) : Move (i+1) L (.hub i) i L
  | leaf {h L i} (mem : i ∈ L) : Move h L (.leaf i) h (L.erase i)

def Fits (h : ℕ) (L : Finset ℕ) := ∀ i ∈ L, i < h

def Eligible (h i : ℕ) := h % 2 = 1 ∨ i+1 ≠ h

def Policy (w : ℕ → ℝ) (h : ℕ) (L : Finset ℕ) : Token → Prop
  | .hub _ => h % 2 = 0
  | .leaf i => (h % 2 = 1 ∨ h-1 ∈ L) ∧ Eligible h i ∧
      ∀ j ∈ L, Eligible h j → w j ≤ w i

theorem move_fits {h L x h' L'} (m : Move h L x h' L') (fit : Fits h L) : Fits h' L' := by
  cases m with
  | @hub i L free =>
    intro j hj
    have := fit j hj
    have : j ≠ h' := fun e => free (e ▸ hj)
    omega
  | leaf mem => exact fun j hj => fit j (mem_of_mem_erase hj)

theorem move_size {h L x h' L'} (m : Move h L x h' L') : h'+L'.card+1=h+L.card := by
  cases m with
  | hub free => omega
  | leaf mem => rw [card_erase_of_mem mem]; have := card_pos.mpr ⟨_,mem⟩; omega

theorem policy_exists (w : ℕ → ℝ) {h L} (fit : Fits h L) (pos : 0<h+L.card)
    (even : (h+L.card)%2=0) :
    ∃ x h' L', Move h L x h' L' ∧ Policy w h L x := by
  classical
  have hp : 0<h := by
    by_contra! hz
    have : L=∅ := eq_empty_iff_forall_notMem.mpr (fun j hj => by have := fit j hj; omega)
    simp_all
  by_cases force : h%2=0 ∧ h-1∉L
  · obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
    exact ⟨_,_,_,Move.hub (by simpa using force.2),force.1⟩
  have anyLeaf : (L.filter (Eligible h)).Nonempty := by
    by_contra! empty
    have only : L ⊆ {h-1} := by
      intro j hj
      have ne : ¬ Eligible h j := fun el => by
        have hm : j∈L.filter (Eligible h) := mem_filter.mpr ⟨hj,el⟩
        rw [empty] at hm
        exact notMem_empty j hm
      simp only [Eligible,not_or,not_not] at ne
      simp only [mem_singleton]; omega
    have bound := card_le_card only
    simp only [card_singleton] at bound
    by_cases odd : h%2=1
    · have : L.Nonempty := card_pos.mp (by omega)
      obtain ⟨j,hj⟩ := this
      have el : Eligible h j := Or.inl odd
      have := mem_filter.mpr ⟨hj,el⟩
      rw [empty] at this
      exact notMem_empty j this
    · have ht : h-1∈L := by by_contra hn; exact force ⟨by omega,hn⟩
      have := card_pos.mpr ⟨_,ht⟩
      omega
  obtain ⟨i,hi,largest⟩ := (L.filter (Eligible h)).exists_max_image w anyLeaf
  obtain ⟨mem,ok⟩ := mem_filter.mp hi
  refine ⟨_,_,_,Move.leaf mem,?_,ok,fun j hj ej => largest j (mem_filter.mpr ⟨hj,ej⟩)⟩
  by_cases odd : h%2=1
  · exact Or.inl odd
  · exact Or.inr (by by_contra hn; exact force ⟨by omega,hn⟩)

noncomputable def count (w : ℕ → ℝ) (t : ℝ) (L : Finset ℕ) :=
  (L.filter fun i => t ≤ w i).card

noncomputable def hit (w : ℕ → ℝ) (t : ℝ) : Token → ℕ
  | .hub _ => 0
  | .leaf i => if t ≤ w i then 1 else 0

noncomputable def bonus (w : ℕ → ℝ) (t : ℝ) (h : ℕ) (L : Finset ℕ) : ℕ :=
  if h%2=1 ∨ (h-1∈L ∧ w (h-1)<t) then 1 else 0

noncomputable def quota (w : ℕ → ℝ) (t : ℝ) (h : ℕ) (L : Finset ℕ) :=
  (count w t L+bonus w t h L)/2

private theorem count_move (w : ℕ → ℝ) (t : ℝ) {h L x k M}
    (m : Move h L x k M) : count w t M + hit w t x = count w t L := by
  cases m with
  | hub => rfl
  | @leaf h L i mem =>
    unfold count
    rw [filter_erase]
    by_cases hi : t ≤ w i
    · have hm : i ∈ L.filter (fun j => t ≤ w j) := mem_filter.mpr ⟨mem,hi⟩
      simp only [hit,ite_eq_left hi,card_erase_of_mem hm]
      have := card_pos.mpr ⟨_,hm⟩
      omega
    · simp [hit,hi]

private theorem bonus_le (w : ℕ → ℝ) (t : ℝ) (h L) : bonus w t h L ≤ 1 := by
  unfold bonus
  split <;> omega

/-- One round of the same weight-based policy pays its quota at every threshold. -/
theorem quota_round (w : ℕ → ℝ) (t : ℝ) {h L a k M b g N}
    (ma : Move h L a k M) (p : Policy w h L a) (mb : Move k M b g N) :
    quota w t h L ≤ hit w t a + quota w t g N := by
  have ca := count_move w t ma
  have cb := count_move w t mb
  have ba := bonus_le w t h L
  unfold quota
  cases ma with
  | @hub i L free =>
    change (k+1)%2=0 at p
    have z : bonus w t (k+1) L=0 := by simp [bonus, free, show (k+1)%2≠1 by omega]
    simp only [hit] at ca ⊢
    cases mb with
    | hub => simp only [hit] at cb; omega
    | @leaf _ _ j mem =>
      have one : bonus w t k (L.erase j)=1 := by simp [bonus,show k%2=1 by omega]
      simp only [hit] at cb
      split at cb <;> omega
  | @leaf h L i mem =>
    obtain ⟨safe,ei,largest⟩ := p
    by_cases high : t≤w i
    · simp only [hit,ite_eq_left high] at ca ⊢
      cases mb with
      | hub => simp only [hit] at cb; omega
      | @leaf _ _ j mj =>
        by_cases hj : t≤w j
        · simp only [hit,ite_eq_left hj] at cb
          have keep : bonus w t h L ≤ bonus w t h ((L.erase i).erase j) := by
            unfold bonus
            split
            · rename_i cond
              have cond' : h%2=1 ∨ (h-1 ∈ (L.erase i).erase j ∧ w (h-1)<t) := by
                rcases cond with odd | ⟨ht,low⟩
                · exact Or.inl odd
                · have ni : h-1 ≠ i := by intro e; rw [e] at low; linarith
                  have nj : h-1 ≠ j := by intro e; rw [e] at low; linarith
                  exact Or.inr ⟨mem_erase.mpr ⟨nj,mem_erase.mpr ⟨ni,ht⟩⟩,low⟩
              simp only [ite_eq_left cond',le_refl]
            · omega
          omega
        · simp only [hit,ite_eq_right hj] at cb
          omega
    · have unique : ∀ j∈L, t≤w j → j=h-1 ∧ h%2=0 := by
        intro j hj hi
        have ne : ¬Eligible h j := fun ej => high (hi.trans (largest j hj ej))
        simp only [Eligible,not_or,not_not] at ne
        omega
      by_cases existsHigh : ∃ j∈L, t≤w j
      · obtain ⟨j,hj,hij⟩ := existsHigh
        obtain ⟨eq,par⟩ := unique j hj hij
        have small : count w t L ≤ 1 := by
          unfold count
          calc
            _ ≤ ({h-1} : Finset ℕ).card := card_le_card (by
              intro x hx
              obtain ⟨hxL,hi⟩ := mem_filter.mp hx
              exact mem_singleton.mpr (unique x hxL hi).1)
            _ = 1 := card_singleton _
        have z : bonus w t h L=0 := by
          rw [eq] at hij
          simp [bonus,par,not_lt.mpr hij]
        omega
      · have empty : count w t L=0 := by
          apply card_eq_zero.mpr
          apply eq_empty_iff_forall_notMem.mpr
          intro j hj
          exact existsHigh ⟨j,(mem_filter.mp hj).1,(mem_filter.mp hj).2⟩
        omega

/-- A complete play against the policy. Bob may use every legal reply. -/
inductive Play (w : ℕ → ℝ) : ℕ → Finset ℕ → List Token → Prop where
  | nil : Play w 0 ∅ []
  | round {h L a k M b g N xs} (ma : Move h L a k M) (p : Policy w h L a)
      (mb : Move k M b g N) (rest : Play w g N xs) : Play w h L (a::b::xs)

noncomputable def aliceHigh (w : ℕ → ℝ) (t : ℝ) : List Token → ℕ
  | a :: _ :: xs => hit w t a + aliceHigh w t xs
  | _ => 0

theorem threshold_guarantee {w h L xs} (run : Play w h L xs) (t : ℝ) :
    quota w t h L ≤ aliceHigh w t xs := by
  induction run with
  | nil => simp [quota,bonus,count,aliceHigh]
  | round ma p mb rest ih =>
    exact (quota_round w t ma p mb).trans (Nat.add_le_add_left ih _)

private theorem count_full {w : ℕ → ℝ} {t : ℝ} {L : Finset ℕ} (ht : ∀ i∈L,t≤w i) :
    count w t L=L.card := by
  unfold count
  rw [filter_eq_self.mpr ht]

theorem paired_threshold {w v : ℕ → ℝ} {n L R xs ys}
    (forward : Play w n L xs) (backward : Play v n R ys) (evenLeaves : L.card%2=0)
    (top : n-1∈L) (minimum : ∀ i∈L,w (n-1)≤w i)
    (same : ∀ t, count w t L=count v t R) (t : ℝ) :
    count w t L ≤ aliceHigh w t xs + aliceHigh v t ys := by
  have a := threshold_guarantee forward t
  have b := threshold_guarantee backward t
  unfold quota at a b
  rw [← same t] at b
  by_cases low : w (n-1)<t
  · have bonus1 : bonus w t n L=1 := by simp [bonus,top,low]
    omega
  · have all := count_full (fun i hi => (not_lt.mp low).trans (minimum i hi))
    omega

private def hubPart (u : ℕ → ℝ) : Token → ℝ
  | .hub i => u i
  | .leaf _ => 0

private def leafPart (w : ℕ → ℝ) : Token → ℝ
  | .leaf i => w i
  | .hub _ => 0

def bank (f : Token → ℝ) : List Token → ℝ
  | a :: _ :: xs => f a + bank f xs
  | _ => 0

def hubQuota (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i+1 => hubQuota u i + (if i%2=1 then u i else 0)

theorem hub_bank {w h L xs} (run : Play w h L xs) (u : ℕ → ℝ) :
    bank (hubPart u) xs=hubQuota u h := by
  induction run with
  | nil => rfl
  | @round h L a k M b g N xs ma p mb rest ih =>
    simp only [bank,ih]
    cases ma with
    | hub free =>
      change (k+1)%2=0 at p
      have odd : k%2=1 := by omega
      cases mb with
      | hub =>
        simp [hubPart,hubQuota,show g%2≠1 by omega,odd,add_comm]
      | leaf => simp [hubPart,hubQuota,odd,add_comm]
    | @leaf h L i mem =>
      obtain ⟨safe,ei,_⟩ := p
      cases mb with
      | leaf => simp [hubPart]
      | hub free =>
        have hind : g%2≠1 := by
          intro hg
          have ne : (g+1)%2≠1 := by omega
          have ht : g∈L := by simpa using safe.resolve_left ne
          have dif := ei.resolve_left ne
          exact free (mem_erase.mpr ⟨by omega,ht⟩)
        simp [hubPart,hubQuota,hind]

private theorem level_expansion (S : Finset ℝ) (positive : ∀ x∈S,0≤x) :
    ∃ c : ℝ → ℝ, (∀ t∈S,0≤c t) ∧
      ∀ x∈S,x=∑ t∈S, if t≤x then c t else 0 := by
  classical
  induction S using Finset.induction_on_max with
  | empty => exact ⟨fun _ => 0,by simp,by simp⟩
  | insert a S lt ih =>
    have ha : a∉S := fun h => lt_irrefl a (lt a h)
    obtain ⟨c,nn,repr⟩ := ih (fun x hx => positive x (mem_insert_of_mem hx))
    have prev : (∑ t∈S,c t)≤a := by
      rcases S.eq_empty_or_nonempty with rfl|ne
      · simpa using positive a (mem_insert_self ..)
      · have hm := S.max'_mem ne
        have le : ∀ t∈S,t≤S.max' ne := fun t ht => S.le_max' t ht
        have e := repr _ hm
        simp only [sum_congr rfl (fun t ht => ite_eq_left (le t ht))] at e
        rw [← e]
        exact (lt _ hm).le
    let d := fun t => if t=a then a-∑ j∈S,c j else c t
    have old : ∀ t∈S,d t=c t := fun t ht => ite_eq_right (lt t ht).ne
    refine ⟨d,?_,?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · simp [d,prev]
      · rw [old t ht]; exact nn t ht
    · intro x hx
      rw [sum_insert ha]
      rcases mem_insert.mp hx with rfl | hx
      · simp only [le_refl,ite_true]
        have eq : (∑ t∈S,if t≤x then d t else 0)=∑ t∈S,c t :=
          sum_congr rfl (fun t ht => (ite_eq_left (lt t ht).le).trans (old t ht))
        rw [eq]
        simp [d]
      · rw [ite_eq_right (not_le.mpr (lt x hx)),zero_add]
        exact (repr x hx).trans (sum_congr rfl (fun t ht => by rw [old t ht]))

private theorem move_sub {h L x k M} (step : Move h L x k M) : M ⊆ L := by
  cases step with
  | hub => exact Subset.rfl
  | leaf => exact erase_subset ..

private theorem bank_levels {w h L xs} (run : Play w h L xs) (S : Finset ℝ) (c : ℝ → ℝ)
    (repr : ∀ i∈L,w i=∑ t∈S,if t≤w i then c t else 0) :
    bank (leafPart w) xs=∑ t∈S,c t*(aliceHigh w t xs : ℝ) := by
  induction run with
  | nil => simp [bank,aliceHigh]
  | round ma p mb _ ih =>
    simp only [bank,aliceHigh,Nat.cast_add,mul_add,sum_add_distrib]
    rw [ih (fun i hi => repr i (move_sub ma (move_sub mb hi)))]
    congr 1
    cases ma with
    | hub => simp [leafPart,hit]
    | @leaf _ _ i mem =>
      calc
        _ = ∑ t∈S,if t≤w i then c t else 0 := repr i mem
        _ = _ := sum_congr rfl (fun t _ => by by_cases hi : t≤w i <;> simp [hit,hi])

private theorem total_levels {w : ℕ → ℝ} (L : Finset ℕ) (S : Finset ℝ) (c : ℝ → ℝ)
    (repr : ∀ i∈L,w i=∑ t∈S,if t≤w i then c t else 0) :
    ∑ i∈L,w i=∑ t∈S,c t*(count w t L : ℝ) := by
  rw [sum_congr rfl repr,sum_comm]
  apply sum_congr rfl
  intro t ht
  rw [← sum_filter]
  simp [count,mul_comm]

theorem paired_leaf_bank {w v : ℕ → ℝ} {n L R xs ys}
    (forward : Play w n L xs) (backward : Play v n R ys) (evenLeaves : L.card%2=0)
    (top : n-1∈L) (minimum : ∀ i∈L,w (n-1)≤w i)
    (same : ∀ t, count w t L=count v t R)
    (nn : ∀ i∈L,0≤w i) (nn' : ∀ i∈R,0≤v i) :
    ∑ i∈L,w i ≤ bank (leafPart w) xs + bank (leafPart v) ys := by
  let S := L.image w ∪ R.image v
  obtain ⟨c,pos,repr⟩ := level_expansion S (by
    intro x hx
    rcases mem_union.mp hx with hx|hx
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx; exact nn i hi
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx; exact nn' i hi)
  have f := fun i (hi : i∈L) => repr (w i) (mem_union_left _ (mem_image_of_mem w hi))
  have q := fun i (hi : i∈R) => repr (v i) (mem_union_right _ (mem_image_of_mem v hi))
  rw [total_levels L S c f,bank_levels forward S c f,bank_levels backward S c q,
    ← sum_add_distrib]
  apply sum_le_sum
  intro t ht
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (pos t ht)
  exact_mod_cast paired_threshold forward backward evenLeaves top minimum same t

def flip (n i : ℕ) := n-1-i

private theorem flip_twice {n i : ℕ} (lt : i<n) : flip n (flip n i)=i := by
  unfold flip
  omega

theorem count_reverse (w : ℕ → ℝ) {n L} (fit : Fits n L) (t : ℝ) :
    count w t L=count (w ∘ flip n) t (L.image (flip n)) := by
  classical
  have eq : ((L.image (flip n)).filter fun j => t≤w (flip n j)) =
      (L.filter fun i => t≤w i).image (flip n) := by
    ext j
    constructor
    · intro hj
      obtain ⟨hj,high⟩ := mem_filter.mp hj
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
      rw [flip_twice (fit i hi)] at high
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,high⟩,rfl⟩
    · intro hj
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
      obtain ⟨hi,high⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨mem_image_of_mem _ hi,by simpa [flip_twice (fit i hi)]⟩
  unfold count
  simp only [Function.comp_apply,eq]
  symm
  apply card_image_of_injOn
  intro i hi j hj same
  have h1 := fit i (mem_filter.mp hi).1
  have h2 := fit j (mem_filter.mp hj).1
  simpa only [flip_twice h1,flip_twice h2] using congrArg (flip n) same

private theorem hubQuota_sum (u : ℕ → ℝ) (h : ℕ) :
    hubQuota u h=∑ i∈range h,if i%2=1 then u i else 0 := by
  induction h with
  | zero => simp [hubQuota]
  | succ n ih => rw [hubQuota,sum_range_succ,ih]

private theorem complement_hubs (u : ℕ → ℝ) {n : ℕ} (even : n%2=0) :
    hubQuota u n+hubQuota (u ∘ flip n) n = ∑ i∈range n,u i := by
  simp only [hubQuota_sum,Function.comp_apply]
  rw [← sum_range_reflect (fun i => if i%2=1 then u (flip n i) else 0) n,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have lt := mem_range.mp hi
  change (if i%2=1 then u i else 0) +
    (if flip n i%2=1 then u (flip n (flip n i)) else 0) = u i
  rw [flip_twice lt]
  by_cases odd : i%2=1
  · have other : flip n i%2≠1 := by unfold flip; omega
    simp [odd,other]
  · have other : flip n i%2=1 := by unfold flip; omega
    simp [odd,other]

def loot (u w : ℕ → ℝ) : Token → ℝ
  | .hub i => u i
  | .leaf i => w i

private theorem bank_split (u w : ℕ → ℝ) (xs : List Token) :
    bank (loot u w) xs=bank (hubPart u) xs + bank (leafPart w) xs := by
  fun_induction bank (loot u w) xs with
  | case1 a b xs ih =>
    simp only [bank,ih]
    cases a <;> simp [loot,hubPart,leafPart] <;> ac_rfl
  | case2 xs shorter =>
    cases xs with
    | nil => simp [bank]
    | cons a xs => cases xs with
      | nil => simp [bank]
      | cons b xs => exact (shorter a b xs rfl).elim

/-- Across complete plays on opposite roots, the two first-player scores
cover one copy of the entire position. -/
theorem opposite_scores (u w : ℕ → ℝ) {n L xs ys} (fit : Fits n L)
    (even : n%2=0) (evenLeaves : L.card%2=0) (top : n-1∈L)
    (minimum : ∀ i∈L,w (n-1)≤w i) (nn : ∀ i∈L,0≤w i)
    (forward : Play w n L xs) (backward : Play (w ∘ flip n) n (L.image (flip n)) ys) :
    (∑ i∈range n,u i) + ∑ i∈L,w i ≤ bank (loot u w) xs + bank (loot (u ∘ flip n) (w ∘ flip n)) ys := by
  have hr : ∀ i∈L.image (flip n),0≤(w ∘ flip n) i := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    simpa [flip_twice (fit i hi)] using nn i hi
  have leaf := paired_leaf_bank forward backward evenLeaves top minimum (count_reverse w fit) nn hr
  rw [bank_split,bank_split (u ∘ flip n),hub_bank forward,hub_bank backward]
  linarith only [leaf,complement_hubs u even]

def choices (h : ℕ) (L : Finset ℕ) : Finset Token :=
  L.image Token.leaf ∪ (if 0<h ∧ h-1∉L then {Token.hub (h-1)} else ∅)

def nextH (h : ℕ) : Token → ℕ
  | .leaf _ => h
  | .hub i => i

def nextL (L : Finset ℕ) : Token → Finset ℕ
  | .leaf i => L.erase i
  | .hub _ => L

theorem move_choice {h L x k M} (m : Move h L x k M) :
    x∈choices h L ∧ nextH h x=k ∧ nextL L x=M := by
  cases m with
  | hub free => simp [choices,free,nextH,nextL]
  | leaf mem => exact ⟨mem_union_left _ (mem_image_of_mem _ mem),rfl,rfl⟩

theorem choice_move {h L x} (e : x∈choices h L) :
    Move h L x (nextH h x) (nextL L x) := by
  rcases mem_union.mp e with e|e
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp e
    exact Move.leaf hi
  · by_cases b : 0<h ∧ h-1∉L
    · simp only [ite_eq_left b,mem_singleton] at e
      subst x
      cases h with
      | zero => omega
      | succ i => exact Move.hub (by simpa using b.2)
    · simp [b] at e

private theorem nonempty_choices {h L} (fit : Fits h L) (pos : 0<h+L.card) :
    (choices h L).Nonempty := by
  rcases L.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
  · have hp : 0<h := by simpa using pos
    exact ⟨Token.hub (h-1),by simp [choices,hp]⟩
  · exact ⟨_,(move_choice (Move.leaf (h:=h) hi)).1⟩

def mass (u w : ℕ → ℝ) (h : ℕ) (L : Finset ℕ) := (∑ i∈range h,u i) + ∑ i∈L,w i

private theorem mass_step (u w : ℕ → ℝ) {h L x k M} (m : Move h L x k M) :
    mass u w h L = loot u w x + mass u w k M := by
  cases m with
  | hub => simp [mass,sum_range_succ,loot,add_left_comm,add_comm]
  | @leaf _ _ i mem =>
    simp only [mass,loot]
    linarith only [sum_erase_add _ w mem]

/-- Optimal score for the player on move. Every move spends one unit of fuel.
At full fuel the opponent receives the complementary score from the position. -/
noncomputable def score (u w : ℕ → ℝ) : ℕ → ℕ → Finset ℕ → ℝ
  | 0, _, _ => 0
  | k+1, h, L =>
    if ne : (choices h L).Nonempty then
      (choices h L).sup' ne fun x => mass u w h L-score u w k (nextH h x) (nextL L x)
    else 0

private theorem score_lower (u w : ℕ → ℝ) (k : ℕ) {h L x g N} (mv : Move h L x g N) :
    mass u w h L-score u w k g N ≤ score u w (k+1) h L := by
  obtain ⟨hx,eqh,eqL⟩ := move_choice mv
  rw [score,dite_eq_left ⟨x,hx⟩,← eqh,← eqL]
  exact le_sup' (f := fun y => mass u w h L-score u w k (nextH h y) (nextL L y)) hx

private theorem score_attained (u w : ℕ → ℝ) (k : ℕ) {h L}
    (ne : (choices h L).Nonempty) :
    ∃ x g N, Move h L x g N ∧ score u w (k+1) h L=mass u w h L-score u w k g N := by
  rw [score,dite_eq_left ne]
  obtain ⟨x,hx,eq⟩ := (choices h L).exists_mem_eq_sup' ne
    (fun y => mass u w h L-score u w k (nextH h y) (nextL L y))
  exact ⟨_,_,_,choice_move hx,eq⟩

theorem optimal_dominates_policy (u w : ℕ → ℝ) (m : ℕ) {h L}
    (fit : Fits h L) (size : h+L.card=2*m) :
    ∃ xs, Play w h L xs ∧ bank (loot u w) xs≤score u w (2*m) h L := by
  induction m generalizing h L with
  | zero =>
    have hz : h=0 := by omega
    have lz : L=∅ := card_eq_zero.mp (by omega)
    subst h; subst L
    exact ⟨[],Play.nil,le_refl _⟩
  | succ m ih =>
    obtain ⟨a,k,M,ma,p⟩ := policy_exists w fit (by omega) (by omega)
    have cut := move_size ma
    obtain ⟨b,g,N,mb,best⟩ := score_attained u w (2*m)
      (nonempty_choices (move_fits ma fit) (by omega))
    have cut' := move_size mb
    obtain ⟨xs,tr,bound⟩ := ih (move_fits mb (move_fits ma fit)) (by omega)
    refine ⟨_,Play.round ma p mb tr,?_⟩
    change loot u w a+bank (loot u w) xs ≤ _
    have lo := score_lower u w (2*m+1) ma
    rw [show 2*(m+1)=2*m+1+1 by omega]
    linarith only [lo,best,bound,mass_step u w ma]

noncomputable def margin (u w : ℕ → ℝ) (h : ℕ) (L : Finset ℕ) :=
  2*score u w (h+L.card) h L-mass u w h L

private theorem reverse_card {n L} (fit : Fits n L) : (L.image (flip n)).card=L.card := by
  apply card_image_of_injOn
  intro i hi j hj same
  simpa only [flip_twice (fit i hi),flip_twice (fit j hj)] using congrArg (flip n) same

private theorem reverse_mass (u w : ℕ → ℝ) {n L} (fit : Fits n L) :
    mass (u ∘ flip n) (w ∘ flip n) n (L.image (flip n))=mass u w n L := by
  unfold mass
  simp only [Function.comp_apply]
  rw [show (∑ i∈range n,u (flip n i))=∑ i∈range n,u i from sum_range_reflect u n]
  congr 1
  rw [sum_image]
  · exact sum_congr rfl (fun i hi => congrArg w (flip_twice (fit i hi)))
  · intro i hi j hj same
    simpa only [flip_twice (fit i hi),flip_twice (fit j hj)] using congrArg (flip n) same

/-- On an even spine with an even number of leaves, if the far endpoint
bears a lightest leaf, opposite singleton-rooted optimal margins sum to at least zero. -/
theorem opposite_margins (u w : ℕ → ℝ) {n L} (fit : Fits n L)
    (even : n%2=0) (evenLeaves : L.card%2=0) (top : n-1∈L)
    (minimum : ∀ i∈L,w (n-1)≤w i) (nn : ∀ i∈L,0≤w i) :
    0≤margin u w n L+margin (u ∘ flip n) (w ∘ flip n) n (L.image (flip n)) := by
  have card := reverse_card fit
  let m := (n+L.card)/2
  have size : n+L.card=2*m := by dsimp [m]; omega
  have revFit : Fits n (L.image (flip n)) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    have := fit i hi
    unfold flip
    omega
  obtain ⟨xs,fw,fx⟩ := optimal_dominates_policy u w m fit size
  obtain ⟨ys,bw,by'⟩ := optimal_dominates_policy (u ∘ flip n) (w ∘ flip n) m revFit
    (by simpa only [card] using size)
  have bound := opposite_scores u w fit even evenLeaves top minimum nn fw bw
  change mass u w n L ≤ _ at bound
  unfold margin
  rw [reverse_mass u w fit,card,size]
  linarith only [bound,fx,by']

#print axioms opposite_margins

end GraphGrabbing.Comb
