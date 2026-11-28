import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

namespace ArmstrongRibbons

/-- Weight coordinates of a point of the fundamental box for `a = 6`. -/
abbrev Point := Fin 6 × Fin 6 × Fin 6 × Fin 6 × Fin 6

/-- The five suffix sums, in order from longest to shortest. -/
def suffix (x : Point) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let ⟨a, b, c, d, e⟩ := x
  (a.val + b.val + c.val + d.val + e.val,
    b.val + c.val + d.val + e.val, c.val + d.val + e.val, d.val + e.val, e.val)

def total (x : Point) : ℕ := (suffix x).1

def height (x : Point) : ℕ :=
  let ⟨a, b, c, d, e⟩ := suffix x
  a + b + c + d + e

/-- Armstrong's tilted order, Definition 10.1. -/
def suffixLE (x y : Point) : Prop :=
  let ⟨a, b, c, d, e⟩ := suffix x
  let ⟨f, g, h, i, j⟩ := suffix y
  a ≤ f ∧ b ≤ g ∧ c ≤ h ∧ d ≤ i ∧ e ≤ j

instance (x y : Point) : Decidable (suffixLE x y) := by
  unfold suffixLE
  split; split; infer_instance

def Cover (S : Set Point) (x y : Point) : Prop :=
  x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ suffixLE x y ∧
    ∀ z ∈ S, suffixLE x z → suffixLE z y → z = x ∨ z = y

def RibbonPartition (S : Set Point) : Prop :=
  ∃ ribbons : List (List Point),
    ribbons.flatten.Nodup ∧
    (∀ x, x ∈ ribbons.flatten ↔ x ∈ S) ∧
    ∀ row ∈ ribbons, row.length = 6 ∧
      row.IsChain (fun x y => Cover S x y ∧ height y = height x + 1)

private theorem height_mono {x y : Point} (h : suffixLE x y) : height x ≤ height y := by
  rcases x with ⟨a, b, c, d, e⟩
  rcases y with ⟨f, g, i, j, k⟩
  simp only [suffixLE, suffix, height] at *
  omega

private theorem eq_of_height_eq {x y : Point} (h : suffixLE x y) (he : height x = height y) :
    x = y := by
  rcases x with ⟨a, b, c, d, e⟩
  rcases y with ⟨f, g, i, j, k⟩
  simp only [suffixLE, suffix, height, Prod.mk.injEq, Fin.ext_iff] at *
  omega

theorem cover_of_step {S : Set Point} {x y : Point} (hx : x ∈ S) (hy : y ∈ S)
    (h : suffixLE x y ∧ height y = height x + 1) : Cover S x y := by
  refine ⟨hx, hy, ?_, h.1, ?_⟩
  · rintro rfl
    omega
  · intro z _ hxz hzy
    have h₁ := height_mono hxz
    have h₂ := height_mono hzy
    by_cases hz : height x = height z
    · exact Or.inl (eq_of_height_eq hxz hz).symm
    · exact Or.inr (eq_of_height_eq hzy (by omega))

def Slice (lo hi : ℤ) : Set Point := {x | lo ≤ (total x : ℤ) ∧ (total x : ℤ) ≤ hi}

private def decode (n : ℕ) : Point :=
  (⟨n / 1296 % 6, by omega⟩, ⟨n / 216 % 6, by omega⟩,
   ⟨n / 36 % 6, by omega⟩, ⟨n / 6 % 6, by omega⟩, ⟨n % 6, by omega⟩)

private def encode (x : Point) : ℕ :=
  let ⟨a, b, c, d, e⟩ := x
  1296 * a.val + 216 * b.val + 36 * c.val + 6 * d.val + e.val

private theorem decode_encode (x : Point) : decode (encode x) = x := by
  rcases x with ⟨a, b, c, d, e⟩
  simp only [decode, encode, Prod.mk.injEq, Fin.ext_iff]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  omega

private theorem encode_lt (x : Point) : encode x < 7776 := by
  rcases x with ⟨a, b, c, d, e⟩
  simp only [encode]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  omega

private theorem encode_decode {n : ℕ} (h : n < 7776) : encode (decode n) = n := by
  simp only [encode, decode]
  omega

/-- The encoded points in a chunk of the box whose weight sums lie in the slice. -/
def selectedRange (lo hi start count : ℕ) : List ℕ :=
  (List.range' start count).filter fun n =>
    decide (lo ≤ total (decode n) ∧ total (decode n) ≤ hi)

def selected (lo hi : ℕ) : List ℕ := selectedRange lo hi 0 7776

private theorem mem_selected {lo hi n : ℕ} :
    n ∈ selected lo hi ↔ n < 7776 ∧ decode n ∈ Slice lo hi := by
  change n ∈ selected lo hi ↔
    n < 7776 ∧ ((lo : ℤ) ≤ (total (decode n) : ℤ) ∧ (total (decode n) : ℤ) ≤ hi)
  simp [selected, selectedRange]

private theorem selected_exact {lo hi : ℕ} {x : Point} :
    x ∈ (selected lo hi).map decode ↔ x ∈ Slice lo hi := by
  rw [List.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact (mem_selected.mp hn).2
  · intro hx
    exact ⟨encode x, mem_selected.mpr ⟨encode_lt x, by simpa [decode_encode] using hx⟩,
      decode_encode x⟩

abbrev step (x y : Point) : Prop := suffixLE x y ∧ height y = height x + 1

private def chainCheck : List Point → Bool
  | x :: y :: rest => decide (suffixLE x y ∧ height y = height x + 1) && chainCheck (y :: rest)
  | _ => true

private theorem chainCheck_sound : ∀ r, chainCheck r = true → r.IsChain step
  | [], _ => .nil
  | [_], _ => .singleton _
  | x :: y :: rest, h => by
    rw [chainCheck, Bool.and_eq_true] at h
    exact List.isChain_cons_cons.mpr ⟨of_decide_eq_true h.1, chainCheck_sound _ h.2⟩

def rowCheck (row : List ℕ) : Bool :=
  (row.length == 6) && chainCheck (row.map decode)

/-- Bit `n` records whether code `n` has appeared. Reject repeated codes. -/
private def addCode (acc : Option ℕ) (n : ℕ) : Option ℕ :=
  match acc with
  | none => none
  | some mask => if mask.testBit n then none else some (mask ||| (1 <<< n))

def pack (seed : Option ℕ) (codes : List ℕ) : Option ℕ := codes.foldl addCode seed

private theorem pack_none (codes : List ℕ) : pack none codes = none := by
  induction codes with
  | nil => rfl
  | cons n ns ih => exact ih

private theorem singleton_bit (n i : ℕ) : (1 <<< n).testBit i = true ↔ i = n := by
  rw [Nat.testBit_shiftLeft]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
  omega

private theorem added_bit (seed n i : ℕ) :
    (seed ||| (1 <<< n)).testBit i = true ↔ seed.testBit i = true ∨ i = n := by
  rw [Nat.testBit_or, Bool.or_eq_true, singleton_bit]

private theorem pack_sound {codes : List ℕ} {seed mask : ℕ}
    (h : pack (some seed) codes = some mask) :
    codes.Nodup ∧
    (∀ i ∈ codes, seed.testBit i = false) ∧
    (∀ i, mask.testBit i = true ↔ seed.testBit i = true ∨ i ∈ codes) := by
  induction codes generalizing seed with
  | nil =>
    have heq : seed = mask := Option.some.inj h
    subst mask
    simp
  | cons n ns ih =>
    change pack (addCode (some seed) n) ns = some mask at h
    cases hn : seed.testBit n with
    | true => simp [addCode, hn, pack_none] at h
    | false =>
      simp only [addCode, hn, Bool.false_eq_true, ite_false] at h
      obtain ⟨hdup, hfresh, hbits⟩ := ih h
      have hf (i : ℕ) (hi : i ∈ ns) : ¬ (seed.testBit i = true ∨ i = n) := by
        rw [← added_bit, hfresh i hi]
        decide
      refine ⟨List.nodup_cons.mpr ⟨fun hi => hf n hi (Or.inr rfl), hdup⟩, ?_, ?_⟩
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hn
        · cases he : seed.testBit i
          · rfl
          · exact (hf i hi (Or.inl he)).elim
      · intro i
        rw [hbits i, added_bit, List.mem_cons, or_assoc]

private theorem pack_append (seed : Option ℕ) (xs ys : List ℕ) :
    pack seed (xs ++ ys) = pack (pack seed xs) ys :=
  List.foldl_append

theorem pack_rows_append {xs ys : List (List ℕ)} {a b c : ℕ}
    (hx : pack (some a) xs.flatten = some b)
    (hy : pack (some b) ys.flatten = some c) :
    pack (some a) (xs ++ ys).flatten = some c := by
  rw [List.flatten_append, pack_append, hx, hy]

theorem pack_selected_append {lo hi start count tail a b c : ℕ}
    (hx : pack (some a) (selectedRange lo hi start count) = some b)
    (hy : pack (some b) (selectedRange lo hi (start + count) tail) = some c) :
    pack (some a) (selectedRange lo hi start (count + tail)) = some c := by
  have hr : selectedRange lo hi start (count + tail) =
      selectedRange lo hi start count ++ selectedRange lo hi (start + count) tail := by
    unfold selectedRange
    rw [← List.range'_append_1, List.filter_append]
  rw [hr, pack_append, hx, hy]

theorem rowCheck_append {xs ys : List (List ℕ)}
    (hx : xs.all rowCheck = true) (hy : ys.all rowCheck = true) :
    (xs ++ ys).all rowCheck = true := by
  rw [List.all_append, hx, hy]
  rfl

theorem partitionOfCertificate (lo hi : ℕ) (rows : List (List ℕ)) (mask : ℕ)
    (hpoints : pack (some 0) rows.flatten = some mask)
    (hselected : pack (some 0) (selected lo hi) = some mask)
    (hrows : rows.all rowCheck = true) : RibbonPartition (Slice lo hi) := by
  let ribbons := rows.map (List.map decode)
  have hflat : ribbons.flatten = rows.flatten.map decode := List.map_flatten.symm
  have hcode {n : ℕ} : n ∈ rows.flatten ↔ n ∈ selected lo hi := by
    have h₁ := (pack_sound hpoints).2.2 n
    have h₂ := (pack_sound hselected).2.2 n
    simpa using h₁.symm.trans h₂
  have hmem : ∀ x, x ∈ ribbons.flatten ↔ x ∈ Slice lo hi := by
    intro x
    rw [← selected_exact, hflat, List.mem_map, List.mem_map]
    exact exists_congr fun n => and_congr_left fun _ => hcode
  refine ⟨ribbons, ?_, hmem, ?_⟩
  · rw [hflat]
    apply List.Nodup.map_on _ (pack_sound hpoints).1
    intro n hn m hm heq
    simpa [encode_decode (mem_selected.mp (hcode.mp hn)).1,
      encode_decode (mem_selected.mp (hcode.mp hm)).1] using congrArg encode heq
  · intro row hrow
    obtain ⟨codes, hcodes, rfl⟩ := List.mem_map.mp hrow
    have hr : rowCheck codes = true := List.all_eq_true.mp hrows _ hcodes
    rw [rowCheck, Bool.and_eq_true, beq_iff_eq] at hr
    refine ⟨by simpa using hr.1, (chainCheck_sound _ hr.2).imp_of_mem_imp ?_⟩
    intro x y hx hy hstep
    exact ⟨cover_of_step (hmem x |>.mp (List.mem_flatten_of_mem hrow hx))
      (hmem y |>.mp (List.mem_flatten_of_mem hrow hy)) hstep, hstep.2⟩

end ArmstrongRibbons
