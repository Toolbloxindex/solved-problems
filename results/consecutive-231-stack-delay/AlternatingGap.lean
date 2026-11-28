import OptionalProjection

namespace SC231

private abbrev ScanState := Word × Word

private def advance (state : ScanState) (c : Nat) : ScanState :=
  match state with
  | (b :: a :: tail, log) =>
      if a < c ∧ c < b then (c :: a :: tail, b :: log)
      else (c :: b :: a :: tail, log)
  | (stack, log) => (c :: stack, log)

private def read (input : Word) (state : ScanState) : ScanState :=
  input.foldl advance state

private theorem read_cons (c : Nat) (input : Word) (state : ScanState) :
    read (c :: input) state = read input (advance state c) := rfl

private theorem read_append (first last : Word) (state : ScanState) :
    read (first ++ last) state = read last (read first state) := List.foldl_append

private theorem advance_push_of_top_le {b c : Nat} (h : b ≤ c) (tail log : Word) :
    advance (b :: tail, log) c = (c :: b :: tail, log) := by
  cases tail with
  | nil => rfl
  | cons a tail => simp [advance, Nat.not_lt_of_ge h]

private theorem advance_push_of_le_below {a b c : Nat} (h : c ≤ a) (tail log : Word) :
    advance (b :: a :: tail, log) c = (c :: b :: a :: tail, log) := by
  simp [advance, Nat.not_lt_of_ge h]

private theorem advance_pop {a b c : Nat} (ha : a < c) (hb : c < b) (tail log : Word) :
    advance (b :: a :: tail, log) c = (c :: a :: tail, b :: log) := by
  simp [advance, ha, hb]

private theorem scan_eq_read (input stack log : Word) :
    deterministicScan input stack log =
      (read input (stack, log)).2.reverse ++ (read input (stack, log)).1 := by
  induction input generalizing stack log with
  | nil => rfl
  | cons c input ih =>
    rw [read_cons]
    cases stack with
    | nil => exact ih _ _
    | cons b tail =>
      cases tail with
      | nil => exact ih _ _
      | cons a tail =>
        by_cases h : a < c ∧ c < b
        · simpa only [deterministicScan, advance, ite_eq_left h] using ih (c :: a :: tail) (b :: log)
        · simpa only [deterministicScan, advance, ite_eq_right h] using ih (c :: b :: a :: tail) log

private def High (word : Word) : Prop := ∀ x ∈ word, 8 < x

private def StartsLow : Word → Prop
  | [] => True
  | x :: _ => x ≤ 8

private theorem high_cons {x : Nat} {word : Word} (hx : 8 < x) (hw : High word) :
    High (x :: word) := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact hw y hy

private theorem high_append {x y : Word} (hx : High x) (hy : High y) : High (x ++ y) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hx a ha
  · exact hy a ha

private theorem high_reverse {word : Word} (h : High word) : High word.reverse := by
  intro x hx
  exact h x (List.mem_reverse.mp hx)

private theorem project_high {word : Word} (h : High word) : project 8 word = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  simpa using Nat.not_le_of_gt (h x hx)

private theorem advance_high {front tail log : Word} {c : Nat}
    (hf : High front) (ht : StartsLow tail) (hl : High log) (hc : 8 < c) :
    ∃ front' log', High front' ∧ High log' ∧
      advance (front ++ tail, log) c = (front' ++ tail, log') := by
  have pushResult (h : advance (front ++ tail, log) c = (c :: (front ++ tail), log)) :
      ∃ front' log', High front' ∧ High log' ∧
        advance (front ++ tail, log) c = (front' ++ tail, log') :=
    ⟨c :: front, log, high_cons hc hf, hl, h⟩
  cases front with
  | nil =>
    apply pushResult
    cases tail with
    | nil => rfl
    | cons b tail =>
      change b ≤ 8 at ht
      exact advance_push_of_top_le (show b ≤ c by omega) tail log
  | cons b rest =>
    have hb := hf b (by simp)
    have hr : High rest := fun x hx => hf x (by simp [hx])
    cases h : rest ++ tail with
    | nil => exact pushResult (by simp [h, advance])
    | cons a remaining =>
      by_cases hp : a < c ∧ c < b
      · exact ⟨c :: rest, b :: log, high_cons hc hr, high_cons hb hl,
          by simp [h, advance, hp]⟩
      · exact pushResult (by simp [h, advance, hp])

private theorem read_high {input front tail log : Word}
    (hi : High input) (hf : High front) (ht : StartsLow tail) (hl : High log) :
    ∃ front' log', High front' ∧ High log' ∧
      read input (front ++ tail, log) = (front' ++ tail, log') := by
  induction input generalizing front log with
  | nil => exact ⟨front, log, hf, hl, rfl⟩
  | cons c input ih =>
    obtain ⟨front', log', hf', hl', hstep⟩ :=
      advance_high hf ht hl (hi c (by simp))
    obtain ⟨front'', log'', hf'', hl'', hread⟩ :=
      ih (fun x hx => hi x (by simp [hx])) hf' hl'
    exact ⟨front'', log'', hf'', hl'', by rw [read_cons, hstep, hread]⟩

private def anchor (side : Bool) : Word :=
  if side then [8, 6, 3, 1] else [7, 4, 2, 5]

/-- A flank is stored from the summit outward, with its four low letters last. -/
private inductive Flank (side : Bool) : Word → Prop
  | base : Flank side (anchor side)
  | grow {x : Nat} {word : Word} :
      8 < x → (∀ y ∈ word, y < x) → Flank side word → Flank side (x :: word)

private theorem flank_exists_cons {side : Bool} {word : Word} (h : Flank side word) :
    ∃ x rest, word = x :: rest := by
  cases h with
  | base => cases side <;> exact ⟨_, _, rfl⟩
  | grow => exact ⟨_, _, rfl⟩

private theorem flank_head_mem {side : Bool} {word : Word} (h : Flank side word) :
    word.headD 0 ∈ word := by
  obtain ⟨x, rest, rfl⟩ := flank_exists_cons h
  simp

private theorem flank_projection {side : Bool} {word : Word} (h : Flank side word) :
    project 8 word = anchor side := by
  induction h with
  | base => cases side <;> rfl
  | grow hx hbound h ih =>
    simpa [project, Nat.not_le_of_gt hx] using ih

private theorem flank_low_end {side : Bool} {word : Word} (h : Flank side word) :
    ∃ x tail, x ≤ 8 ∧ word.reverse = x :: tail := by
  induction h with
  | base => cases side <;> exact ⟨_, _, by decide, rfl⟩
  | @grow new word hnew hbound h ih =>
    obtain ⟨x, tail, hx, htail⟩ := ih
    exact ⟨x, tail ++ [new], hx, by simp [htail]⟩

private theorem advance_low_on_high {c : Nat} {stack log : Word}
    (hc : c ≤ 8) (hs : High stack) :
    advance (stack, log) c = (c :: stack, log) := by
  cases stack with
  | nil => rfl
  | cons b rest =>
    cases rest with
    | nil => rfl
    | cons a tail =>
      have ha := hs a (by simp)
      exact advance_push_of_le_below (by omega) tail log

private theorem advance_second_low {first second : Nat} {stack log : Word}
    (hs : High stack) (hc : second ≤ 8) :
    advance (first :: stack, log) second = (second :: first :: stack, log) := by
  cases stack with
  | nil => rfl
  | cons a tail =>
    have ha := hs a (by simp)
    exact advance_push_of_le_below (by omega) tail log

/-- Reading inward up a flank retains every entry. -/
private theorem read_inward {side : Bool} {word stack log : Word}
    (h : Flank side word) (hs : High stack) :
    read word.reverse (stack, log) = (word ++ stack, log) := by
  induction h with
  | base =>
    cases side
    · change read [5, 2, 4, 7] (stack, log) = (7 :: 4 :: 2 :: 5 :: stack, log)
      rw [read_cons, advance_low_on_high (by decide) hs,
          read_cons, advance_second_low hs (by decide)]
      rfl
    · change read [1, 3, 6, 8] (stack, log) = (8 :: 6 :: 3 :: 1 :: stack, log)
      rw [read_cons, advance_low_on_high (by decide) hs,
          read_cons, advance_second_low hs (by decide)]
      rfl
  | @grow x word hx hbound h ih =>
    rw [List.reverse_cons, read_append, ih]
    obtain ⟨b, tail, rfl⟩ := flank_exists_cons h
    have hb := hbound b (by simp)
    change advance (b :: (tail ++ stack), log) x = (x :: b :: (tail ++ stack), log)
    exact advance_push_of_top_le (Nat.le_of_lt hb) (tail ++ stack) log

/-- Once the first outward letter is pushed below a larger letter, the rest stays. -/
private theorem read_outward {side : Bool} {word : Word} (h : Flank side word)
    (b : Nat) (stack log : Word) (hb : word.headD 0 ≤ b) :
    read word.tail (word.headD 0 :: b :: stack, log) =
      (word.reverse ++ b :: stack, log) := by
  induction h generalizing b stack log with
  | base =>
    cases side
    · change 7 ≤ b at hb
      change read [4, 2, 5] (7 :: b :: stack, log) = (5 :: 2 :: 4 :: 7 :: b :: stack, log)
      rw [read_cons, advance_push_of_le_below (show 4 ≤ b by omega)]
      rfl
    · change 8 ≤ b at hb
      change read [6, 3, 1] (8 :: b :: stack, log) = (1 :: 3 :: 6 :: 8 :: b :: stack, log)
      rw [read_cons, advance_push_of_le_below (show 6 ≤ b by omega)]
      rfl
  | @grow x word hx hbound h ih =>
    obtain ⟨c, rest, rfl⟩ := flank_exists_cons h
    have hc := hbound c (by simp)
    change x ≤ b at hb
    change read (c :: rest) (x :: b :: stack, log) =
      (((x :: c :: rest).reverse) ++ b :: stack, log)
    rw [read_cons, advance_push_of_le_below (show c ≤ b by omega)]
    simpa only [List.headD_cons, List.tail_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.cons_append, List.nil_append] using
      ih x (b :: stack) log (by simpa using Nat.le_of_lt hc)


private structure Gap where
  left : Word
  top : Nat
  right : Word

private def Gap.word (g : Gap) : Word := g.left.reverse ++ g.top :: g.right

private def Gap.flip (g : Gap) : Gap := ⟨g.right, g.top, g.left⟩

private def Gap.grow (g : Gap) : Gap := ⟨g.right, g.top + 1, g.top :: g.left⟩

private theorem Gap.flip_flip (g : Gap) : g.flip.flip = g := by
  cases g
  rfl

private theorem Gap.word_flip (g : Gap) : g.flip.word = g.word.reverse := by
  simp [Gap.word, Gap.flip, List.append_assoc]

private theorem Gap.word_grow (g : Gap) :
    g.grow.word = g.right.reverse ++ (g.top + 1) :: g.top :: g.left := rfl

private theorem Gap.word_flip_startsLow {g : Gap} {side : Bool}
    (h : Flank side g.right) : StartsLow g.word.reverse := by
  obtain ⟨a, tail, ha, hrev⟩ := flank_low_end h
  rw [← g.word_flip]
  simpa [Gap.word, Gap.flip, hrev, StartsLow] using ha

private structure GapShape (g : Gap) (side : Bool) : Prop where
  left : Flank side g.left
  right : Flank (!side) g.right
  topHigh : 8 < g.top
  topBound : ∀ x ∈ g.left ++ g.right, x < g.top
  openPeak : g.left.headD 0 < g.right.headD 0

private theorem GapShape.left_le {g : Gap} {side : Bool} (h : GapShape g side) :
    g.left.headD 0 < g.top :=
  h.topBound _ (List.mem_append_left _ (flank_head_mem h.left))

private theorem GapShape.right_le {g : Gap} {side : Bool} (h : GapShape g side) :
    g.right.headD 0 < g.top :=
  h.topBound _ (List.mem_append_right _ (flank_head_mem h.right))

private def gap : Nat → Gap
  | 0 => ⟨anchor false, 9, anchor true⟩
  | r + 1 => (gap r).grow

private def orientation : Nat → Bool
  | 0 => false
  | r + 1 => !(orientation r)

private theorem orientation_parity (r : Nat) : orientation r = true ↔ r % 2 = 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
    change (!(orientation r) = true) ↔ (r + 1) % 2 = 1
    cases he : orientation r <;> simp [he] at ih ⊢ <;> omega

private theorem gap_shape (r : Nat) : GapShape (gap r) (orientation r) := by
  induction r with
  | zero => exact ⟨.base, .base, by decide, by decide, by decide⟩
  | succ r ih =>
    let g := gap r
    change GapShape g.grow (!(orientation r))
    refine ⟨ih.right, ?_, ?_, ?_, ih.right_le⟩
    · simpa [Gap.grow] using
        Flank.grow ih.topHigh (fun x hx => ih.topBound x (List.mem_append_left _ hx)) ih.left
    · exact Nat.lt_succ_of_lt ih.topHigh
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Nat.lt_succ_of_lt (ih.topBound x (List.mem_append_right _ hx))
      · rcases List.mem_cons.mp hx with he | hx
        · simp [Gap.grow, he]
        · exact Nat.lt_succ_of_lt (ih.topBound x (List.mem_append_left _ hx))

private theorem gap_top (r : Nat) : (gap r).top = r + 9 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (gap r).top + 1 = r + 1 + 9
    omega

private theorem read_cold_tail {side : Bool} {right : Word} (hr : Flank side right)
    {a p : Nat} (remain log : Word) (hskip : right.headD 0 ≤ a)
    (hdown : right.headD 0 ≤ p) :
    read right (p :: a :: remain, log) = (right.reverse ++ p :: a :: remain, log) := by
  obtain ⟨c, rest, rfl⟩ := flank_exists_cons hr
  change c ≤ a at hskip
  rw [read_cons, advance_push_of_le_below hskip]
  exact read_outward hr p (a :: remain) log hdown

/-- An oriented summit with a larger left witness stays during this pass. -/
private theorem read_cold {left right stack log : Word} {p : Nat} {l r : Bool}
    (hl : Flank l left) (hr : Flank r right) (hs : High stack)
    (hup : left.headD 0 ≤ p) (hdown : right.headD 0 ≤ p)
    (hskip : right.headD 0 ≤ left.headD 0) :
    read (Gap.word ⟨left, p, right⟩) (stack, log) =
      ((Gap.word ⟨left, p, right⟩).reverse ++ stack, log) := by
  obtain ⟨a, remain, rfl⟩ := flank_exists_cons hl
  change a ≤ p at hup
  change right.headD 0 ≤ a at hskip
  change read ((a :: remain).reverse ++ p :: right) (stack, log) = _
  rw [read_append, read_inward hl hs, read_cons]
  simp only [List.cons_append]
  rw [advance_push_of_top_le hup, read_cold_tail hr _ _ hskip hdown]
  simp [Gap.word, List.append_assoc]

/-- A new, larger summit immediately before an old cold summit is the only pop. -/
private theorem read_extra {left right stack log : Word} {p q : Nat} {l r : Bool}
    (hl : Flank l left) (hr : Flank r right) (hs : High stack)
    (hup : left.headD 0 < p) (hdown : right.headD 0 ≤ p)
    (hskip : right.headD 0 ≤ left.headD 0) (hpq : p < q) :
    read (left.reverse ++ q :: p :: right) (stack, log) =
      ((Gap.word ⟨left, p, right⟩).reverse ++ stack, q :: log) := by
  obtain ⟨a, remain, rfl⟩ := flank_exists_cons hl
  change a < p at hup
  change right.headD 0 ≤ a at hskip
  rw [read_append, read_inward hl hs, read_cons]
  simp only [List.cons_append]
  rw [advance_push_of_top_le (show a ≤ q by omega), read_cons,
      advance_pop hup hpq, read_cold_tail hr _ _ hskip hdown]
  simp [Gap.word, List.append_assoc]

/-- A high exterior stays exterior on either side of the fixed core. -/
private theorem frame_pass {front back core surviving : Word}
    (hf : High front) (hb : High back) (ht : StartsLow surviving.reverse)
    (hne : surviving.reverse ≠ [])
    (hc : ∀ stack log, High stack → High log →
      ∃ newLog, High newLog ∧ read core (stack, log) = (surviving.reverse ++ stack, newLog)) :
    ∃ front' back', High front' ∧ High back' ∧
      deterministicScan (front ++ core ++ back) [] [] = front' ++ surviving.reverse ++ back' := by
  have hnil : High [] := by simp [High]
  obtain ⟨stack, log, hs, hl, hread⟩ :=
    read_high (front := []) (tail := []) (log := []) hf hnil trivial hnil
  simp only [List.append_nil] at hread
  obtain ⟨newLog, hnewLog, hcore⟩ := hc stack log hs hl
  have ht' : StartsLow (surviving.reverse ++ stack) := by
    cases h : surviving.reverse with
    | nil => exact (hne h).elim
    | cons a rest => simpa [h, StartsLow] using ht
  obtain ⟨top, finalLog, htop, hlog, hback⟩ :=
    read_high (front := []) (tail := surviving.reverse ++ stack)
      (log := newLog) hb hnil ht' hnewLog
  simp only [List.nil_append] at hback
  refine ⟨finalLog.reverse ++ top, stack, high_append (high_reverse hlog) htop, hs, ?_⟩
  rw [scan_eq_read, read_append, read_append, hread, hcore, hback]
  simp [List.append_assoc]


private theorem Gap.reverse_ne_nil (g : Gap) : g.word.reverse ≠ [] := by
  rw [← g.word_flip]
  simp [Gap.word, Gap.flip]

private def Framed (g : Gap) (word : Word) : Prop :=
  ∃ front back, High front ∧ High back ∧ word = front ++ g.word ++ back

private theorem start_gap (r : Nat) :
    Framed (gap r) (deterministicScan (gap r).flip.word [] []) := by
  let g := gap r
  have h := gap_shape r
  have hn : High [] := by simp [High]
  have hr := g.flip.word_flip_startsLow h.left
  obtain ⟨front, back, hf, hb, hh⟩ :=
    frame_pass (core := g.flip.word) (surviving := g.flip.word)
      hn hn hr g.flip.reverse_ne_nil (by
        intro stack log hs hl
        exact ⟨log, hl, read_cold h.right h.left hs (Nat.le_of_lt h.right_le)
          (Nat.le_of_lt h.left_le) (Nat.le_of_lt h.openPeak)⟩)
  rw [← g.flip.word_flip, Gap.flip_flip] at hh
  exact ⟨front, back, hf, hb, by simpa only [List.nil_append, List.append_nil] using hh⟩

private theorem peel_gap {r : Nat} {word : Word} (hw : Framed (gap (r + 1)) word) :
    Framed (gap r) (deterministicScan word [] []) := by
  obtain ⟨front, back, hf, hb, rfl⟩ := hw
  let g := gap r
  have h := gap_shape r
  obtain ⟨front', back', hf', hb', hh⟩ :=
    frame_pass (core := g.grow.word) (surviving := g.flip.word)
      hf hb (g.flip.word_flip_startsLow h.left) g.flip.reverse_ne_nil (by
        intro stack log hs hl
        exact ⟨(g.top + 1) :: log, high_cons (Nat.lt_succ_of_lt h.topHigh) hl,
          read_extra h.right h.left hs h.right_le (Nat.le_of_lt h.left_le)
            (Nat.le_of_lt h.openPeak) (Nat.lt_succ_self _)⟩)
  rw [← g.flip.word_flip, Gap.flip_flip] at hh
  exact ⟨front', back', hf', hb', hh⟩

private theorem framed_project {g : Gap} {side : Bool} {word : Word}
    (hl : Flank side g.left) (hr : Flank (!side) g.right) (hp : 8 < g.top)
    (hw : Framed g word) :
    project 8 word = if side then base.reverse else base := by
  obtain ⟨front, back, hf, hb, rfl⟩ := hw
  have happ (u v : Word) : project 8 (u ++ v) = project 8 u ++ project 8 v :=
    List.filter_append u v
  have hrev (u : Word) : project 8 u.reverse = (project 8 u).reverse := List.filter_reverse
  have ht : project 8 (g.top :: g.right) = project 8 g.right := by
    simp [project, Nat.not_le_of_gt hp]
  simp only [Gap.word, happ, hrev, ht, flank_projection hl, flank_projection hr,
    project_high hf, project_high hb, List.nil_append, List.append_nil]
  cases side <;> rfl

private theorem run_add (word : Word) (s t : Nat) :
    run word (s + t) = run (run word s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change deterministicScan (run word (s + t)) [] [] =
      deterministicScan (run (run word s) t) [] []
    rw [ih]

private theorem run_framed {word : Word} {r t : Nat} (ht : t ≤ r)
    (hw : Framed (gap r) word) : Framed (gap (r - t)) (run word t) := by
  induction t with
  | zero => exact hw
  | succ t ih =>
    have hh := ih (Nat.le_of_succ_le ht)
    have he : r - t = (r - (t + 1)) + 1 := by omega
    rw [he] at hh
    exact peel_gap hh

/-- For positive padding, start in the closed orientation. -/
def paddedSeed : Nat → Word
  | 0 => base
  | r + 1 => (gap r).flip.word

private theorem padded_framed {r t : Nat} (ht : t ≤ r) :
    Framed (gap (r - t)) (run (paddedSeed (r + 1)) (t + 1)) := by
  rw [show t + 1 = 1 + t by omega, run_add]
  exact run_framed ht (start_gap r)

/-- Up to and including the padding time, no low letter has changed its relative order
except for complete reversals. -/
theorem padded_projection_parity {m t : Nat} (ht : t ≤ m) :
    project 8 (run (paddedSeed m) t) = if t % 2 = m % 2 then base else base.reverse := by
  cases m with
  | zero =>
    have h : t = 0 := by omega
    subst t
    decide
  | succ r =>
    cases t with
    | zero =>
      have h := gap_shape r
      have hn : High [] := by simp [High]
      have hframe : Framed (gap r).flip (paddedSeed (r + 1)) :=
        ⟨[], [], hn, hn, by simp [paddedSeed]⟩
      have hp := framed_project (g := (gap r).flip) (side := !(orientation r)) h.right
        (by simpa [Gap.flip] using h.left) h.topHigh hframe
      change project 8 (paddedSeed (r + 1)) =
        (if 0 = (r + 1) % 2 then base else base.reverse)
      rw [hp]
      have hpar := orientation_parity r
      cases he : orientation r with
      | false =>
        simp [he] at hpar
        have hne : 0 ≠ (r + 1) % 2 := by omega
        simp [hne]
      | true =>
        simp [he] at hpar
        have heq : 0 = (r + 1) % 2 := by omega
        simp [heq]
    | succ t =>
      have h := gap_shape (r - t)
      have hp := framed_project h.left h.right h.topHigh (padded_framed (by omega : t ≤ r))
      rw [hp]
      have hpar := orientation_parity (r - t)
      cases he : orientation (r - t) with
      | false =>
        simp [he] at hpar
        have heq : (t + 1) % 2 = (r + 1) % 2 := by omega
        simp [heq]
      | true =>
        simp [he] at hpar
        have hne : (t + 1) % 2 ≠ (r + 1) % 2 := by omega
        simp [hne]

theorem padded_projection_prefix {m t : Nat} (ht : t ≤ m) :
    project 8 (run (paddedSeed m) t) = base ∨
    project 8 (run (paddedSeed m) t) = base.reverse := by
  rw [padded_projection_parity ht]
  split <;> simp

theorem padded_projection_at_time (m : Nat) :
    project 8 (run (paddedSeed m) m) = base := by
  simp [padded_projection_parity (Nat.le_refl m)]

private theorem gap_perm (r : Nat) : (gap r).word.Perm (List.range' 1 (r + 9)) := by
  induction r with
  | zero => decide
  | succ r ih =>
    let g := gap r
    change g.grow.word.Perm (List.range' 1 (r + 1 + 9))
    have hnew : g.grow.word.Perm ((g.top + 1) :: g.flip.word) :=
      List.perm_middle
    have hold : g.flip.word.Perm (List.range' 1 (r + 9)) :=
      (g.word_flip ▸ List.reverse_perm g.word : g.flip.word.Perm g.word).trans ih
    have hs : r + 1 + 9 = (r + 9) + 1 := by omega
    rw [hs, List.range'_1_concat]
    refine (hnew.trans (hold.cons _)).trans ?_
    have hp : g.top + 1 = 1 + (r + 9) := by
      change (gap r).top + 1 = 1 + (r + 9)
      rw [gap_top]
      omega
    rw [hp]
    exact (List.perm_append_singleton _ _).symm

theorem paddedSeed_perm (m : Nat) : (paddedSeed m).Perm (List.range' 1 (m + 8)) := by
  cases m with
  | zero => decide
  | succ r =>
    change (gap r).flip.word.Perm (List.range' 1 (r + 9))
    rw [Gap.word_flip]
    exact ((gap r).word.reverse_perm).trans (gap_perm r)

/-- For every n ≥ 8 a literal permutation of [n] avoids the periodic set through
pass n + 2 under the source's consecutive-231 stack map. -/
theorem consecutive231_max_delay_lower_bound (n : Nat) (hn : 8 ≤ n) :
    ∃ word : Word, word.Perm (List.range' 1 n) ∧
      ∀ t : Nat, t < n + 3 → ¬ IsTarget (run word t) := by
  let m := n - 8
  have hm : m + 8 = n := by omega
  refine ⟨paddedSeed m, hm ▸ paddedSeed_perm m, ?_⟩
  intro t ht
  by_cases h : t < m
  · intro htarget
    have htarg : IsTarget (project 8 (run (paddedSeed m) t)) :=
      fun sub => htarget (sub.trans List.filter_sublist)
    rcases padded_projection_prefix (Nat.le_of_lt h) with hbase | hrev
    · rw [hbase] at htarg
      exact hasPeak_excludes_target _ (by decide) htarg
    · rw [hrev] at htarg
      exact hasPeak_excludes_target _ (by decide) htarg
  · have he : t = m + (t - m) := by omega
    rw [he, run_add]
    exact projected_base_delays_eleven (padded_projection_at_time m) (by omega)

end SC231
