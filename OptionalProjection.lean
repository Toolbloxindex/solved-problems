module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace SC231

abbrev Word := List Nat

/-- The scan uses a top-first stack and a reverse chronological pop log. -/
inductive OptionalScan : Word → Word → Word → Word → Prop
  | finish (stack log : Word) : OptionalScan [] stack log (log.reverse ++ stack)
  | push {c : Nat} {input stack log output : Word} :
      OptionalScan input (c :: stack) log output →
      OptionalScan (c :: input) stack log output
  | pop {a b c : Nat} {input stack log output : Word} :
      a < c → c < b →
      OptionalScan input (c :: a :: stack) (b :: log) output →
      OptionalScan (c :: input) (b :: a :: stack) log output

def project (k : Nat) (word : Word) : Word := word.filter (· ≤ k)

theorem project_optional_scan (k : Nat) {input stack log output : Word}
    (h : OptionalScan input stack log output) :
    OptionalScan (project k input) (project k stack) (project k log) (project k output) := by
  induction h with
  | finish stack log =>
      simpa [project] using OptionalScan.finish (project k stack) (project k log)
  | @push c input stack log output h ih =>
      by_cases hc : c ≤ k
      · simpa [project, hc] using
          OptionalScan.push (c := c) (input := project k input) (stack := project k stack)
            (log := project k log) (output := project k output)
            (by simpa [project, hc] using ih)
      · simpa [project, hc] using ih
  | @pop a b c input stack log output hac hcb h ih =>
      by_cases hb : b ≤ k
      · have hc : c ≤ k := by omega
        have ha : a ≤ k := by omega
        simpa [project, ha, hb, hc] using
          OptionalScan.pop hac hcb (input := project k input) (stack := project k stack)
            (log := project k log) (output := project k output)
            (by simpa [project, ha, hb, hc] using ih)
      · by_cases hc : c ≤ k
        · simpa [project, hb, hc] using
            OptionalScan.push (c := c) (input := project k input)
              (stack := project k (a :: stack)) (log := project k log)
              (output := project k output) (by simpa [project, hb, hc] using ih)
        · simpa [project, hb, hc] using ih

/-- At most one premature pop is possible on each input letter. -/
def deterministicScan : Word → Word → Word → Word
  | [], stack, log => log.reverse ++ stack
  | c :: input, b :: a :: stack, log =>
      if a < c ∧ c < b then deterministicScan input (c :: a :: stack) (b :: log)
      else deterministicScan input (c :: b :: a :: stack) log
  | c :: input, stack, log => deterministicScan input (c :: stack) log

theorem deterministic_scan_is_optional (input stack log : Word) :
    OptionalScan input stack log (deterministicScan input stack log) := by
  induction input generalizing stack log with
  | nil => exact OptionalScan.finish stack log
  | cons c input ih =>
      cases stack with
      | nil => exact OptionalScan.push (ih [c] log)
      | cons b stack =>
          cases stack with
          | nil => exact OptionalScan.push (ih [c, b] log)
          | cons a stack =>
              by_cases h : a < c ∧ c < b
              · simpa [deterministicScan, h] using
                  OptionalScan.pop h.1 h.2 (ih (c :: a :: stack) (b :: log))
              · simpa [deterministicScan, h] using OptionalScan.push (ih (c :: b :: a :: stack) log)

theorem project_deterministic_pass (word : Word) (k : Nat) :
    OptionalScan (project k word) [] [] (project k (deterministicScan word [] [])) :=
  project_optional_scan k (deterministic_scan_is_optional word [] [])

def scanChoices : Word → Word → Word → List Word
  | [], stack, log => [log.reverse ++ stack]
  | c :: input, stack, log =>
      scanChoices input (c :: stack) log ++
        match stack with
        | b :: a :: rest =>
          if a < c ∧ c < b then scanChoices input (c :: a :: rest) (b :: log) else []
        | _ => []

theorem mem_scanChoices {input stack log output : Word}
    (h : OptionalScan input stack log output) : output ∈ scanChoices input stack log := by
  induction h with
  | finish => simp [scanChoices]
  | push h ih =>
      simp only [scanChoices, List.mem_append]
      exact Or.inl ih
  | pop hac hcb h ih =>
      simp [scanChoices, hac, hcb, ih]

def base : Word := [5, 2, 4, 7, 8, 6, 3, 1]

def reachable : Nat → List Word
  | 0 => [base]
  | t + 1 => ((reachable t).flatMap (fun word => scanChoices word [] [])).eraseDups

inductive Orbit : Nat → Word → Prop
  | start : Orbit 0 base
  | next {t : Nat} {word output : Word} :
      Orbit t word → OptionalScan word [] [] output → Orbit (t + 1) output

theorem orbit_mem_reachable {t : Nat} {word : Word} (h : Orbit t word) :
    word ∈ reachable t := by
  induction h with
  | start => simp [reachable]
  | next prev pass ih =>
      simp only [reachable, List.mem_eraseDups, List.mem_flatMap]
      exact ⟨_, ih, mem_scanChoices pass⟩

def hasPeak : Word → Bool
  | a :: b :: c :: rest => (a < b && c < b) || hasPeak (b :: c :: rest)
  | _ => false

private theorem finite_check :
    ((List.range 11).all (fun t => (reachable t).all hasPeak)) = true := by
  decide

theorem base_no_optional_valley_before_eleven {t : Nat} {word : Word}
    (ht : t < 11) (h : Orbit t word) : hasPeak word = true := by
  have hrows := List.all_eq_true.mp finite_check t (List.mem_range.mpr ht)
  exact List.all_eq_true.mp hrows word (orbit_mem_reachable h)

def run (word : Word) : Nat → Word :=
  Nat.rec word (fun _ previous => deterministicScan previous [] [])

theorem orbit_of_projected_run {word : Word} (hbase : project 8 word = base) (t : Nat) :
    Orbit t (project 8 (run word t)) := by
  induction t with
  | zero => simpa [run, hbase] using Orbit.start
  | succ t ih =>
      exact Orbit.next ih (project_deterministic_pass (run word t) 8)

/-- The source periodic set written as classical 132,231 avoidance. -/
def IsTarget (word : Word) : Prop :=
  ∀ {a b c : Nat}, List.Sublist [a, b, c] word → ¬ (a < b ∧ c < b)

theorem hasPeak_excludes_target (word : Word) (h : hasPeak word = true) :
    ¬ IsTarget word := by
  match word with
  | a :: b :: c :: rest =>
      intro htarget
      have hh : (a < b ∧ c < b) ∨ hasPeak (b :: c :: rest) = true := by
        simpa [hasPeak, Bool.and_eq_true, Bool.or_eq_true] using h
      rcases hh with hhere | htail
      · exact htarget (.cons_cons _ (.cons_cons _ (.cons_cons _ (List.nil_sublist _)))) hhere
      · exact hasPeak_excludes_target _ htail (fun sub => htarget (.cons _ sub))
  | [] | [_] | [_, _] => simp [hasPeak] at h

theorem projected_base_delays_eleven {word : Word} (hbase : project 8 word = base)
    {t : Nat} (ht : t < 11) : ¬ IsTarget (run word t) := by
  intro htarget
  have peak := base_no_optional_valley_before_eleven ht (orbit_of_projected_run hbase t)
  exact hasPeak_excludes_target _ peak
    (fun sub => htarget (sub.trans (List.filter_sublist)))

end SC231
