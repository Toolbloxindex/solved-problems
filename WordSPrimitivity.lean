module

public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.Sublists

@[expose] public section

namespace WordSPrimitivity

open List

variable {α : Type*}

/-- An occurrence that uses the displayed letter between `left` and `right`. -/
def Uses (word left : List α) (mark : α) (right : List α) : Prop :=
  ∃ pre post, word = pre ++ mark :: post ∧ pre <+ left ∧ post <+ right

/-- Each source position has its own occurrence of the same word. -/
def Covers (word source : List α) : Prop :=
  ∀ left mark right, source = left ++ mark :: right → Uses word left mark right

private theorem take_sublist_of_embedding {word source : List α}
    {f : Fin word.length ↪o Fin source.length} (letters : ∀ i, word.get i = source.get (f i))
    (a : Fin word.length) : word.take a.val <+ source.take (f a).val := by
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  have hWord : (word.take a.val).length = a.val := by simp
  have hSource : (source.take (f a).val).length = (f a).val := by
    simp
  let inside (i : Fin (word.take a.val).length) : Fin word.length :=
    ⟨i.val, by have := i.isLt; omega⟩
  let restrict (i : Fin (word.take a.val).length) : Fin (source.take (f a).val).length :=
    ⟨(f (inside i)).val, by
      rw [hSource]
      exact f.strictMono (show inside i < a from by have := i.isLt; change i.val < a.val; omega)⟩
  refine ⟨OrderEmbedding.ofStrictMono restrict ?_, ?_⟩
  · intro i j hij
    exact f.strictMono (show inside i < inside j from hij)
  · intro i
    change (word.take a.val).get i = (source.take (f a).val).get (restrict i)
    simpa [restrict, inside, List.get_eq_getElem] using letters (inside i)

private theorem drop_sublist_of_embedding {word source : List α}
    {f : Fin word.length ↪o Fin source.length} (letters : ∀ i, word.get i = source.get (f i))
    (a : Fin word.length) : word.drop (a.val + 1) <+ source.drop ((f a).val + 1) := by
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  have hWord : (word.drop (a.val + 1)).length = word.length - (a.val + 1) := by simp
  have hSource : (source.drop ((f a).val + 1)).length = source.length - ((f a).val + 1) := by simp
  let inside (i : Fin (word.drop (a.val + 1)).length) : Fin word.length :=
    ⟨a.val + 1 + i.val, by have := i.isLt; omega⟩
  have next (i : Fin (word.drop (a.val + 1)).length) : (f a).val + 1 ≤ (f (inside i)).val :=
    f.strictMono (show a < inside i from by change a.val < a.val + 1 + i.val; omega)
  let restrict (i : Fin (word.drop (a.val + 1)).length) :
      Fin (source.drop ((f a).val + 1)).length :=
    ⟨(f (inside i)).val - ((f a).val + 1), by
      have := next i
      have := (f (inside i)).isLt
      omega⟩
  refine ⟨OrderEmbedding.ofStrictMono restrict ?_, ?_⟩
  · intro i j hij
    have h : f (inside i) < f (inside j) :=
      f.strictMono (show inside i < inside j from by
        change a.val + 1 + i.val < a.val + 1 + j.val
        exact Nat.add_lt_add_left hij _)
    change (f (inside i)).val - ((f a).val + 1) < (f (inside j)).val - ((f a).val + 1)
    change (f (inside i)).val < (f (inside j)).val at h
    have := next i
    omega
  · intro i
    change (word.drop (a.val + 1)).get i = (source.drop ((f a).val + 1)).get (restrict i)
    have index : (f a).val + 1 + ((f (inside i)).val - ((f a).val + 1)) = (f (inside i)).val :=
      Nat.add_sub_of_le (next i)
    simpa [restrict, List.get_eq_getElem, List.getElem_drop, inside, index] using letters (inside i)

/-- The authors' position-by-position definition implies the split form of coverage. -/
theorem covers_of_embeddings {word source : List α}
    (h : ∀ i : Fin source.length,
      ∃ f : Fin word.length ↪o Fin source.length,
        (∀ j, word.get j = source.get (f j)) ∧ ∃ j, f j = i) : Covers word source := by
  intro left mark right eq
  let i : Fin source.length := ⟨left.length, by rw [eq]; simp⟩
  obtain ⟨f, letters, j, hj⟩ := h i
  have mark_eq : source.get i = mark := by simp [i, eq, List.get_eq_getElem]
  have letter : word.get j = mark := (letters j).trans (hj ▸ mark_eq)
  refine ⟨word.take j.val, word.drop (j.val + 1), ?_, ?_, ?_⟩
  · rw [← letter, List.get_eq_getElem, List.getElem_cons_drop]
    exact (List.take_append_drop _ _).symm
  · simpa [hj, i, eq] using take_sublist_of_embedding letters j
  · simpa [hj, i, eq] using drop_sublist_of_embedding letters j

private theorem split_unique {d : α} {p q u v : List α} (hp : d ∉ p) (hq : d ∉ q)
    (h : p ++ d :: u = q ++ d :: v) : p = q ∧ u = v := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simpa using h
    | cons x xs =>
      have hd : d = x := (List.cons.inj h).1
      exact (hq (hd ▸ List.mem_cons_self)).elim
  | cons x xs ih =>
    cases q with
    | nil =>
      have hd : x = d := (List.cons.inj h).1
      exact (hp (hd ▸ List.mem_cons_self)).elim
    | cons y ys =>
      obtain ⟨rfl, ht⟩ := List.cons.inj h
      obtain ⟨rfl, rfl⟩ := ih (fun m => hp (.tail _ m)) (fun m => hq (.tail _ m)) ht
      exact ⟨rfl, rfl⟩

private theorem split_last_unique {d : α} {p q u v : List α} (hu : d ∉ u) (hv : d ∉ v)
    (h : p ++ d :: u = q ++ d :: v) : p = q ∧ u = v := by
  have hr : u.reverse ++ d :: p.reverse = v.reverse ++ d :: q.reverse := by
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using congrArg List.reverse h
  obtain ⟨hs, ht⟩ := split_unique (by simpa using hu) (by simpa using hv) hr
  exact ⟨List.reverse_injective ht, List.reverse_injective hs⟩

variable [DecidableEq α]

private theorem first_split_of_mem {d : α} {word : List α} (h : d ∈ word) :
    ∃ p q, word = p ++ d :: q ∧ d ∉ p := by
  induction word with
  | nil => simp at h
  | cons a tail ih =>
    by_cases he : a = d
    · subst a
      exact ⟨[], tail, rfl, by simp⟩
    · have ht : d ∈ tail := by simpa [Ne.symm he] using h
      obtain ⟨p, q, rfl, hp⟩ := ih ht
      exact ⟨a :: p, q, rfl, by simp [Ne.symm he, hp]⟩

private theorem split_saturated {d : α} {p q left right : List α} (hp : d ∉ p)
    (hl : d ∉ left) (hc : right.count d ≤ q.count d)
    (h : p ++ d :: q <+ left ++ d :: right) : p <+ left ∧ q <+ right := by
  obtain ⟨u, v, he, hu, hv⟩ := List.sublist_append_iff.mp h
  have hun : d ∉ u := fun m => hl (hu.subset m)
  rcases List.sublist_cons_iff.mp hv with skip | ⟨tail, rfl, take⟩
  · have hbound := skip.count_le d
    have hpu : p.count d = 0 := List.count_eq_zero.mpr hp
    have huu : u.count d = 0 := List.count_eq_zero.mpr hun
    have counts := congrArg (List.count d) he
    simp [hpu, huu] at counts
    omega
  · obtain ⟨rfl, rfl⟩ := split_unique hp hun he
    exact ⟨hu, take⟩

private theorem split_single {d : α} {word left right : List α} (h : word <+ left ++ d :: right)
    (hm : d ∈ word) (hl : d ∉ left) (hr : d ∉ right) :
    ∃ p q, word = p ++ d :: q ∧ p <+ left ∧ q <+ right := by
  obtain ⟨p, q, rfl, hp⟩ := first_split_of_mem hm
  have hc : right.count d ≤ q.count d := by simp [List.count_eq_zero.mpr hr]
  obtain ⟨hleft, hright⟩ := split_saturated hp hl hc h
  exact ⟨p, q, rfl, hleft, hright⟩

/-- If every copy of the separating letter is used, every local position is still covered. -/
private theorem covers_split {d : α} {p q left right : List α} (hp : d ∉ p)
    (hl : d ∉ left) (hc : q.count d = right.count d)
    (h : Covers (p ++ d :: q) (left ++ d :: right)) : Covers p left ∧ Covers q right := by
  constructor
  · rintro before mark after rfl
    obtain ⟨u, v, he, hu, hv⟩ := h before mark (after ++ d :: right) (by simp)
    have hub : d ∉ u := fun m => hl (List.mem_append_left _ (hu.subset m))
    have hmark : mark ≠ d := fun eq => hl (by simp [eq])
    have hafter : d ∉ after := fun m => hl (by simp [m])
    have hdv : d ∈ v := by
      have hmem : d ∈ p ++ d :: q := by simp
      rw [he] at hmem
      simpa [hub, Ne.symm hmark] using hmem
    obtain ⟨x, y, rfl, hx⟩ := first_split_of_mem hdv
    have hclean : d ∉ u ++ mark :: x := by simp [hub, Ne.symm hmark, hx]
    have he' : p ++ d :: q = (u ++ mark :: x) ++ d :: y := by simpa using he
    obtain ⟨rfl, rfl⟩ := split_unique hp hclean he'
    have hmid := (split_saturated hx hafter hc.ge hv).1
    exact ⟨u, x, rfl, hu, hmid⟩
  · rintro before mark after rfl
    obtain ⟨u, v, he, hu, hv⟩ := h (left ++ d :: before) mark after (by simp)
    have hvc := hv.count_le d
    have hcounts := congrArg (List.count d) he
    simp only [List.count_append, List.count_cons, beq_self_eq_true, ↓reduceIte,
      List.count_eq_zero.mpr hp] at hcounts hc
    have hbefore : before.count d ≤ u.count d := by omega
    have hdu : d ∈ u := by
      apply List.count_pos_iff.mp
      omega
    obtain ⟨x, y, rfl, hx⟩ := first_split_of_mem hdu
    have he' : p ++ d :: q = x ++ d :: (y ++ mark :: v) := by simpa using he
    obtain ⟨rfl, rfl⟩ := split_unique hp hx he'
    have hneed : before.count d ≤ y.count d := by
      simp only [List.count_append, List.count_cons] at hc
      omega
    exact ⟨y, v, rfl, (split_saturated hp hl hneed hu).2, hv⟩

/-- Check a marked occurrence by testing the split at each position in the word. -/
private def checkUses (left right : List Char) (mark : Char) (revPre : List Char) :
    List Char → Bool
  | [] => false
  | x :: xs =>
    (x == mark && revPre.reverse.isSublist left && xs.isSublist right) ||
      checkUses left right mark (x :: revPre) xs

private theorem checkUses_of_sublist {left right pre post : List Char} {mark : Char}
    (hpost : post <+ right) (revPre : List Char) (hpre : revPre.reverse ++ pre <+ left) :
    checkUses left right mark revPre (pre ++ mark :: post) = true := by
  induction pre generalizing revPre with
  | nil =>
    have h : revPre.reverse <+ left := by simpa using hpre
    simp [checkUses, h, hpost]
  | cons a pre ih =>
    have h := ih (a :: revPre) (by simpa [List.reverse_cons, List.append_assoc] using hpre)
    simp [checkUses, h]

private theorem checkUses_of_uses {word left right : List Char} {mark : Char}
    (h : Uses word left mark right) : checkUses left right mark [] word = true := by
  obtain ⟨pre, post, rfl, hpre, hpost⟩ := h
  exact checkUses_of_sublist hpost [] hpre

private def checkSource (word : List Char) (revLeft : List Char) : List Char → Bool
  | [] => true
  | mark :: tail => checkUses revLeft.reverse tail mark [] word && checkSource word (mark :: revLeft) tail

private theorem checkSource_of_covers {word : List Char} (revLeft right : List Char)
    (h : Covers word (revLeft.reverse ++ right)) : checkSource word revLeft right = true := by
  induction right generalizing revLeft with
  | nil => rfl
  | cons mark tail ih =>
    have hm := checkUses_of_uses (h revLeft.reverse mark tail rfl)
    have ht := ih (mark :: revLeft) (by simpa [List.reverse_cons, List.append_assoc] using h)
    simp [checkSource, hm, ht]

def source : List Char := "abacadbabdcabcbadac".toList

private def block₁ : List Char := "abaca".toList
private def block₂ : List Char := "bab".toList
private def block₃ : List Char := "cabcba".toList
private def block₄ : List Char := "ac".toList

private theorem mark_mem_prefix {d x : α} {p q left right : List α}
    (hp : d ∉ p) (hl : d ∉ left) (hx : x ≠ d)
    (h : Uses (p ++ d :: q) left x right) : x ∈ p := by
  obtain ⟨u, v, he, hu, _⟩ := h
  have hdu : d ∉ u := fun m => hl (hu.subset m)
  have hdv : d ∈ v := by
    have hmem : d ∈ p ++ d :: q := by simp
    rw [he] at hmem
    simpa [hdu, Ne.symm hx] using hmem
  obtain ⟨a, b, rfl, ha⟩ := first_split_of_mem hdv
  have he' : p ++ d :: q = (u ++ x :: a) ++ d :: b := by simpa using he
  have same := split_unique hp (by simp [hdu, Ne.symm hx, ha]) he'
  rw [same.1]
  simp

private theorem final_ac {word pre post : List Char} (h : Covers word source)
    (hword : word = pre ++ 'd' :: post) (hpost : post <+ block₄) : post = block₄ := by
  obtain ⟨l₁₉, r₁₉, w₁₉, _, h₁₉⟩ := h (source.take 18) 'c' [] rfl
  rw [List.sublist_nil.mp h₁₉] at w₁₉
  have endsC : word.reverse = 'c' :: l₁₉.reverse := by
    simpa [List.reverse_append, List.reverse_cons] using congrArg List.reverse w₁₉
  obtain ⟨l₁₈, r₁₈, w₁₈, _, h₁₈⟩ := h (source.take 17) 'a' ['c'] rfl
  have r_cases : r₁₈ = [] ∨ r₁₈ = ['c'] := by
    rcases List.sublist_cons_iff.mp h₁₈ with skip | ⟨rest, rfl, take⟩
    · exact Or.inl (List.sublist_nil.mp skip)
    · exact Or.inr (by rw [List.sublist_nil.mp take])
  rcases r_cases with r₁₈empty | r₁₈c
  · rw [r₁₈empty] at w₁₈
    have endsA : word.reverse = 'a' :: l₁₈.reverse := by
      simpa [List.reverse_append, List.reverse_cons] using congrArg List.reverse w₁₈
    exact ((by decide : 'c' ≠ 'a') (List.cons.inj (endsC.symm.trans endsA)).1).elim
  · rw [r₁₈c] at w₁₈
    have endsAC : word.reverse = 'c' :: 'a' :: l₁₈.reverse := by
      simpa [List.reverse_append, List.reverse_cons] using congrArg List.reverse w₁₈
    have endsPost : word.reverse = post.reverse ++ 'd' :: pre.reverse := by
      simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using congrArg List.reverse hword
    have equal := endsPost.symm.trans endsAC
    cases post with
    | nil => exact ((by decide : 'd' ≠ 'c') (List.cons.inj equal).1).elim
    | cons x tail =>
      cases tail with
      | nil => exact ((by decide : 'd' ≠ 'a') (List.cons.inj (List.cons.inj equal).2).1).elim
      | cons y rest =>
        apply hpost.eq_of_length_le
        change 2 ≤ (x :: y :: rest).length
        simp

private def firstPieces : List (List Char) :=
  block₁.sublists.filter fun p => p.head? == some 'a' && p.contains 'b' && p.contains 'c'

private def fewD : List (List Char) :=
  firstPieces.flatMap fun p =>
    (p ++ 'd' :: block₄) :: ((block₂.sublists ++ block₃.sublists).map fun q =>
      p ++ 'd' :: (q ++ 'd' :: block₄))

private theorem coverDecomposition {word : List Char} (h : Covers word source) :
    word ∈ fewD ∨
      ∃ p q t, word = p ++ 'd' :: (q ++ 'd' :: (t ++ 'd' :: block₄)) ∧
        p <+ block₁ ∧ q <+ block₂ ∧ t <+ block₃ := by
  obtain ⟨p, post₆, h₆, hp, _⟩ := h block₁ 'd' (block₂ ++ 'd' :: (block₃ ++ 'd' :: block₄)) rfl
  have cleft : 'd' ∉ block₁ := by decide
  have cright : 'd' ∉ block₄ := by decide
  have hp₀ : 'd' ∉ p := fun m => cleft (hp.subset m)
  have pb : 'b' ∈ p := mark_mem_prefix hp₀ (by decide : 'd' ∉ source.take 1) (by decide) (by
    rw [← h₆]
    exact h (source.take 1) 'b' (source.drop 2) rfl)
  have pc : 'c' ∈ p := mark_mem_prefix hp₀ (by decide : 'd' ∉ source.take 3) (by decide) (by
    rw [← h₆]
    exact h (source.take 3) 'c' (source.drop 4) rfl)
  obtain ⟨l₁, r₁, w₁, h₁, _⟩ := h [] 'a' (source.drop 1) rfl
  rw [List.sublist_nil.mp h₁, List.nil_append] at w₁
  have pa : p.head? = some 'a' := by
    have eq := congrArg List.head? (h₆.symm.trans w₁)
    cases p with
    | nil => exact ((by decide : 'd' ≠ 'a') (Option.some.inj eq)).elim
    | cons x tail => exact eq
  have pmem : p ∈ firstPieces := by
    exact List.mem_filter.mpr ⟨List.mem_sublists.mpr hp, by simp [pa, pb, pc]⟩
  obtain ⟨pre₁₇, post₁₇, h₁₇, _, hpost₁₇⟩ := h
    (block₁ ++ 'd' :: (block₂ ++ 'd' :: block₃)) 'd' block₄ rfl
  rw [final_ac h h₁₇ hpost₁₇] at h₁₇
  obtain ⟨pre, post, he, hpre, hpost⟩ :=
    h (block₁ ++ 'd' :: block₂) 'd' (block₃ ++ 'd' :: block₄) rfl
  have before : pre = p ∨ ∃ q, pre = p ++ 'd' :: q ∧ q <+ block₂ := by
    by_cases hd : 'd' ∈ pre
    · obtain ⟨u, v, eq, hu, hv⟩ := split_single hpre hd cleft (by decide)
      have same := split_unique (fun m => cleft (hu.subset m)) hp₀
        ((by simpa [eq, List.append_assoc] using he.symm :
          u ++ 'd' :: (v ++ 'd' :: post) = word).trans h₆)
      exact Or.inr ⟨v, eq.trans (congrArg (· ++ 'd' :: v) same.1), hv⟩
    · exact Or.inl (split_unique hd hp₀ (he.symm.trans h₆)).1
  have after : post = block₄ ∨ ∃ t, post = t ++ 'd' :: block₄ ∧ t <+ block₃ := by
    by_cases hd : 'd' ∈ post
    · obtain ⟨u, v, eq, hu, hv⟩ := split_single hpost hd (by decide) cright
      have eq' : (pre ++ 'd' :: u) ++ 'd' :: v = word := by
        simpa [eq, List.append_assoc] using he.symm
      have same := split_last_unique (fun m => cright (hv.subset m)) cright (eq'.trans h₁₇)
      exact Or.inr ⟨u, eq.trans (congrArg (fun r => u ++ 'd' :: r) same.2), hu⟩
    · exact Or.inl (split_last_unique hd cright (he.symm.trans h₁₇)).2
  rcases before with rfl | ⟨q, rfl, hq⟩ <;> rcases after with rfl | ⟨t, rfl, ht⟩
  · left
    rw [he]
    exact List.mem_flatMap.mpr ⟨pre, pmem, .head _⟩
  · left
    rw [he]
    exact List.mem_flatMap.mpr ⟨pre, pmem, .tail _ (List.mem_map.mpr
      ⟨t, List.mem_append_right _ (List.mem_sublists.mpr ht), rfl⟩)⟩
  · left
    rw [he]
    simp only [List.append_assoc, List.cons_append]
    exact List.mem_flatMap.mpr ⟨p, pmem, .tail _ (List.mem_map.mpr
      ⟨q, List.mem_append_left _ (List.mem_sublists.mpr hq), rfl⟩)⟩
  · exact Or.inr ⟨p, q, t, by simpa [List.append_assoc] using he, hp, hq, ht⟩

private theorem primitive_of_checked (s : List Char) (hs : s ≠ [])
    (cert : s.sublists.all (fun w => !checkSource w [] s || w == s) = true)
    {w : List Char} (h : Covers w s) : w = s := by
  have hw : w <+ s := by
    cases s with
    | nil => contradiction
    | cons x xs =>
      obtain ⟨p, q, rfl, hp, hq⟩ := h [] x xs rfl
      exact hp.append (hq.cons_cons x)
  have verdict := List.all_eq_true.mp cert w (List.mem_sublists.mpr hw)
  have hc : checkSource w [] s = true := checkSource_of_covers [] s h
  simpa [hc] using verdict

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem primitive (word : List Char) (h : Covers word source) : word = source := by
  rcases coverDecomposition h with hm | ⟨p, q, t, rfl, hp, hq, ht⟩
  · have cert : fewD.any (fun w => checkSource w [] source) = false := by decide +kernel
    have yes : fewD.any (fun w => checkSource w [] source) = true :=
      List.any_eq_true.mpr ⟨word, hm, checkSource_of_covers [] source h⟩
    exact (Bool.noConfusion (cert.symm.trans yes))
  · have hp₀ : 'd' ∉ p := fun m => (by decide : 'd' ∉ block₁) (hp.subset m)
    have hq₀ : 'd' ∉ q := fun m => (by decide : 'd' ∉ block₂) (hq.subset m)
    have ht₀ : 'd' ∉ t := fun m => (by decide : 'd' ∉ block₃) (ht.subset m)
    change Covers (p ++ 'd' :: (q ++ 'd' :: (t ++ 'd' :: block₄)))
      (block₁ ++ 'd' :: (block₂ ++ 'd' :: (block₃ ++ 'd' :: block₄))) at h
    have hc₁ : (q ++ 'd' :: (t ++ 'd' :: block₄)).count 'd' =
        (block₂ ++ 'd' :: (block₃ ++ 'd' :: block₄)).count 'd' := by
      simp [List.count_eq_zero.mpr hq₀, List.count_eq_zero.mpr ht₀]
      decide
    obtain ⟨c₁, h⟩ := covers_split hp₀ (by decide : 'd' ∉ block₁) hc₁ h
    have hc₂ : (t ++ 'd' :: block₄).count 'd' = (block₃ ++ 'd' :: block₄).count 'd' := by
      simp [List.count_eq_zero.mpr ht₀]
      decide
    obtain ⟨c₂, h⟩ := covers_split hq₀ (by decide : 'd' ∉ block₂) hc₂ h
    obtain ⟨c₃, _⟩ := covers_split ht₀ (by decide : 'd' ∉ block₃) rfl h
    rw [primitive_of_checked block₁ (by decide) (by decide +kernel) c₁,
        primitive_of_checked block₂ (by decide) (by decide +kernel) c₂,
        primitive_of_checked block₃ (by decide) (by decide +kernel) c₃]
    rfl

/-- The literal 19-letter word is s-primitive, with an independent embedding at each mark. -/
theorem s_primitive (word : List Char)
    (covers : ∀ i : Fin source.length,
      ∃ f : Fin word.length ↪o Fin source.length,
        (∀ j, word.get j = source.get (f j)) ∧ ∃ j, f j = i) : word = source :=
  primitive word (covers_of_embeddings covers)

#print axioms s_primitive

end WordSPrimitivity
