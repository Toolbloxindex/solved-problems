module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace SC231

abbrev Word := List Nat

def deterministicScan : Word → Word → Word → Word
  | [], stack, log => log.reverse ++ stack
  | c :: input, b :: a :: stack, log =>
      if a < c ∧ c < b then deterministicScan input (c :: a :: stack) (b :: log)
      else deterministicScan input (c :: b :: a :: stack) log
  | c :: input, stack, log => deterministicScan input (c :: stack) log

def run (word : Word) : Nat → Word :=
  Nat.rec word (fun _ previous => deterministicScan previous [] [])

def IsTarget (word : Word) : Prop :=
  ∀ {a b c : Nat}, List.Sublist [a, b, c] word → ¬ (a < b ∧ c < b)

theorem consecutive231_max_delay_lower_bound (n : Nat) (hn : 8 ≤ n) :
    ∃ word : Word, word.Perm (List.range' 1 n) ∧
      ∀ t : Nat, t < n + 3 → ¬ IsTarget (run word t) := by sorry

end SC231
