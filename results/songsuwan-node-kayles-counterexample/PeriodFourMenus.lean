import PeriodFourTarget
import PathMenus
import BoardMap

set_option Elab.async false

namespace KaylesRays.PeriodFourMenus
open LiteralKayles PeriodFourGraph

def coreEdge (a b : Fin 279) : Bool := joinedCore.edge a.val b.val

def marks : Fin 7 → Fin 279 := fun h => ([0,5,30,55,101,177,198] : List (Fin 279))[h.val]?.getD 0

def marked : Finset (Fin 279) := Finset.univ.image marks

def coreBoard (h : Fin 8) : Finset (Fin 279) :=
  if hz : h.val = 0 then Finset.univ
  else drop coreEdge Finset.univ (marks ⟨h.val-1, by omega⟩)

def nearBoard (h : Fin 8) : Finset (Fin 279) := coreBoard h \ marked

def farBoard (h : Fin 8) : Finset (Fin 279) := coreBoard h ∩ marked

def mask (h : Fin 8) : Nat := [15,7,45,71,132,227,247,1271][h.val]?.getD 0

def menu (h : Fin 8) : Finset Nat := (Finset.range 12).filter fun k => mask h |>.testBit k

def erased (h : Fin 8) : Nat := [4,3,1,3,0,2,3,3][h.val]?.getD 0


section Transport

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/-- Relabeling needs to preserve adjacency only among the live vertices. -/
private theorem drop_image (E : V → V → Bool) (D : W → W → Bool)
    (s : Finset V) (f : V → W) (inj : Set.InjOn f (↑s : Set V))
    (pres : ∀ a ∈ s, ∀ b ∈ s, D (f a) (f b) = E a b)
    {v : V} (hv : v ∈ s) :
    drop D (s.image f) (f v) = (drop E s v).image f := by
  ext w
  constructor
  · intro hw
    obtain ⟨hm,hn,he⟩ := Finset.mem_filter.mp hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr
      ⟨hu,fun e => hn (congrArg f e),(pres v hv u hu) ▸ he⟩,rfl⟩
  · rintro hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hm,hn,he⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨u,hm,rfl⟩,
      fun e => hn (inj hm hv e),(pres v hv u hm).trans he⟩


end Transport

/-- Nimber on a disjoint union of three path intervals after two deletions. -/
private theorem path_after_two (n a b : Nat) (ha : a<n) (hb : b<n) (hab : a≤b) :
    value Path.edge (drop Path.edge (drop Path.edge (Finset.range n) a) b) =
      Path.score (a-1) ^^^ Path.score (b-1-(a+2)) ^^^ Path.score (n-(b+2)) := by
  let front := Finset.range (a-1)
  let mid := (Finset.range (b-1-(a+2))).image (fun i => a+2+i)
  let back := (Finset.range (n-(b+2))).image (fun i => b+2+i)
  have mem_mid (v : Nat) : v ∈ mid ↔ a+2≤v ∧ v<b-1 := by
    dsimp [mid]
    simp only [Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨i,hi,rfl⟩
      omega
    · intro h
      exact ⟨v-(a+2),by omega,by omega⟩
  have mem_back (v : Nat) : v ∈ back ↔ b+2≤v ∧ v<n := by
    dsimp [back]
    simp only [Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨i,hi,rfl⟩
      omega
    · intro h
      exact ⟨v-(b+2),by omega,by omega⟩
  have parts : drop Path.edge (drop Path.edge (Finset.range n) a) b = (front∪mid)∪back := by
    ext v
    simp only [drop,Finset.mem_filter,Finset.mem_range,Path.edge,decide_eq_false_iff_not,
      Finset.mem_union,mem_mid,mem_back,front]
    omega
  have gap (i j : Nat) (ij : i+1<j) :
      i ≠ j ∧ Path.edge i j = false ∧ Path.edge j i = false := by
    simp [Path.edge,show i≠j by omega,show i+1≠j by omega,show j+1≠i by omega]
  have fm : Separated Path.edge front mid := by
    intro i hi j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := (mem_mid j).mp hj
    exact gap _ _ (by omega)
  have fb : Separated Path.edge (front∪mid) back := by
    intro i hi j hj
    have hj' := (mem_back j).mp hj
    rcases Finset.mem_union.mp hi with hi|hi
    · have hi' := Finset.mem_range.mp hi
      exact gap _ _ (by omega)
    · have hi' := (mem_mid i).mp hi
      exact gap _ _ (by omega)
  have interval (s len : Nat) : value Path.edge ((Finset.range len).image (fun i => s+i)) =
      Path.score len :=
    value_image _ _ _ _ (fun _ _ _ _ e => by omega) (by
      intro i _ j _
      simp only [Path.edge]
      congr 1
      apply propext
      omega)
  exact parts ▸ ((value_union _ _ _ fb).trans (by
    rw [value_union _ _ _ fm,show value Path.edge mid = _ from interval _ _,
      show value Path.edge back = _ from interval _ _]
    rfl))

private def cycleEdge (n i j : Nat) : Bool := (Factor.cycle n).edge i j

private def rotate (n a i : Nat) : Nat :=
  if a+2+i<n then a+2+i else a+2+i-n

private theorem cycle_relabel (n a : Nat) (hn : 3≤n) (ha : a<n) :
    drop (cycleEdge n) (Finset.range n) a =
      (Finset.range (n-3)).image (rotate n a) := by
  ext v
  simp only [drop,Finset.mem_filter,Finset.mem_range,cycleEdge,Factor.edge,
    decide_eq_false_iff_not,Finset.mem_image]
  constructor
  · intro h
    by_cases hv : a+2≤v
    · refine ⟨v-(a+2),by omega,?_⟩
      unfold rotate
      split <;> omega
    · refine ⟨n+v-(a+2),by omega,?_⟩
      unfold rotate
      split <;> omega
  · rintro ⟨i,hi,rfl⟩
    unfold rotate
    split <;> omega

private theorem rotate_inj (n a : Nat) (hn : 3≤n) (_ha : a<n) :
    Set.InjOn (rotate n a) (↑(Finset.range (n-3)) : Set Nat) := by
  intro i hi j hj hij
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  unfold rotate at hij
  split at hij <;> split at hij <;> omega

private theorem rotate_adj (n a : Nat) (hn : 3≤n) (ha : a<n) :
    ∀ i ∈ Finset.range (n-3), ∀ j ∈ Finset.range (n-3),
      cycleEdge n (rotate n a i) (rotate n a j) = Path.edge i j := by
  intro i hi j hj
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  simp only [cycleEdge,Factor.edge,Path.edge,rotate]
  split <;> split <;> (congr 1; apply propext; omega)

private theorem cycle_after (n a : Nat) (hn : 3≤n) (ha : a<n) :
    value (cycleEdge n) (drop (cycleEdge n) (Finset.range n) a) = Path.score (n-3) := by
  rw [cycle_relabel n a hn ha]
  exact value_image _ _ _ _ (rotate_inj n a hn ha) (rotate_adj n a hn ha)

private theorem cycle_index_lt (n a b : Nat) (hn : 3≤n) (ha : a<n)
    (hb : b ∈ drop (cycleEdge n) (Finset.range n) a) :
    (if a+2≤b then b-(a+2) else n+b-(a+2)) < n-3 := by
  simp only [drop,Finset.mem_filter,Finset.mem_range,cycleEdge,Factor.edge,decide_eq_false_iff_not] at hb
  split <;> omega

private theorem cycle_after_two (n a b : Nat) (hn : 3≤n) (ha : a<n)
    (hb : b ∈ drop (cycleEdge n) (Finset.range n) a) :
    let i := if a+2≤b then b-(a+2) else n+b-(a+2)
    value (cycleEdge n) (drop (cycleEdge n) (drop (cycleEdge n) (Finset.range n) a) b) =
      Path.score (i-1) ^^^ Path.score (n-3-i-2) := by
  rw [cycle_relabel n a hn ha] at hb
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
  have hi' := Finset.mem_range.mp hi
  have index : (if a+2≤rotate n a i then rotate n a i-(a+2)
      else n+rotate n a i-(a+2))=i := by
    unfold rotate
    split <;> split <;> omega
  have rel := drop_image Path.edge (cycleEdge n) (Finset.range (n-3)) (rotate n a)
    (rotate_inj n a hn ha) (rotate_adj n a hn ha) hi
  dsimp
  rw [index,cycle_relabel n a hn ha,rel]
  rw [value_image _ _ _ _
    (fun _ hx _ hy => rotate_inj n a hn ha (drop_sub _ _ _ hx) (drop_sub _ _ _ hy))
    (fun x hx y hy => rotate_adj n a hn ha x (drop_sub _ _ _ hx) y (drop_sub _ _ _ hy))]
  exact Path.option_value hi'

private theorem cycle_value (n : Nat) (hn : 3≤n) :
    value (cycleEdge n) (Finset.range n) = if Path.score (n-3)=0 then 1 else 0 := by
  have opts : Modules.menu (cycleEdge n) (Finset.range n) = {Path.score (n-3)} := by
    ext k
    simp only [Modules.menu,Finset.mem_image,Finset.mem_range,Finset.mem_singleton]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact cycle_after n a hn ha
    · rintro rfl
      exact ⟨0,by omega,cycle_after n 0 hn (by omega)⟩
  rw [value_eq]
  change mex (Modules.menu _ _) = _
  rw [opts]
  apply mex_unique (mex_spec _)
  split
  · rename_i e
    simp only [e,KaylesPair.IsMex,Finset.mem_singleton]
    exact ⟨by decide,by omega⟩
  · rename_i e
    simp [KaylesPair.IsMex,Ne.symm e]

/-- Simultaneous closed-neighborhood deletions, with original labels. -/
private def rest (E : Nat → Nat → Bool) (s : Finset Nat) (ms : List Nat) : Finset Nat :=
  s.filter fun v => ms.all fun m => decide (v ≠ m ∧ E m v = false)

private theorem mem_rest (E : Nat → Nat → Bool) (s : Finset Nat) (ms : List Nat) (v : Nat) :
    v ∈ rest E s ms ↔ v ∈ s ∧ ∀ m ∈ ms, v ≠ m ∧ E m v = false := by
  simp [rest]

private theorem rest_nil (E : Nat → Nat → Bool) (s : Finset Nat) :
    rest E s [] = s := by simp [rest]

private theorem rest_cons (E : Nat → Nat → Bool) (s : Finset Nat) (m : Nat) (ms : List Nat) :
    rest E s (m::ms) = rest E (drop E s m) ms := by
  ext v
  simp only [mem_rest,drop,Finset.mem_filter,List.mem_cons]
  constructor
  · rintro ⟨hv,hm⟩
    exact ⟨⟨hv,hm m (Or.inl rfl)⟩,fun w hw => hm w (Or.inr hw)⟩
  · rintro ⟨⟨hv,hm⟩,ht⟩
    refine ⟨hv,?_⟩
    rintro w (rfl|hw)
    · exact hm
    · exact ht w hw

private def movesLeft (n : Nat) (ms : List Nat) := ms.filter fun v => decide (v<n)
private def movesRight (n : Nat) (ms : List Nat) :=
  (ms.filter fun v => decide (n≤v)).map (·-n)

private def leftLive (j : Bool) (n : Nat) (ms : List Nat) :=
  !j || (ms.all fun v => decide (v<n))
private def rightLive (j : Bool) (n : Nat) (ms : List Nat) :=
  !j || (ms.all fun v => decide (n≤v))

private theorem leftLive_spec (j : Bool) (n : Nat) (ms : List Nat) :
    leftLive j n ms = true ↔ ∀ m ∈ ms, n≤m → j=false := by
  cases j <;> simp [leftLive]

private theorem rightLive_spec (j : Bool) (n : Nat) (ms : List Nat) :
    rightLive j n ms = true ↔ ∀ m ∈ ms, m<n → j=false := by
  cases j <;> simp [rightLive]

private def leftBoard (j : Bool) (l : Factor) (ms : List Nat) :=
  if leftLive j l.order ms then rest l.edge (Finset.range l.order) (movesLeft l.order ms) else ∅

private def rightBoard (j : Bool) (l r : Factor) (ms : List Nat) :=
  if rightLive j l.order ms then rest r.edge (Finset.range r.order) (movesRight l.order ms) else ∅

private theorem mem_leftBoard (j : Bool) (l : Factor) (ms : List Nat) (v : Nat) :
    v ∈ leftBoard j l ms ↔
      leftLive j l.order ms = true ∧
      v<l.order ∧ ∀ m∈ms, m<l.order → v≠m ∧ l.edge m v=false := by
  unfold leftBoard
  split <;> simp_all [mem_rest,movesLeft,List.mem_filter]

private theorem mem_rightBoard (j : Bool) (l r : Factor) (ms : List Nat) (v : Nat) :
    v ∈ rightBoard j l r ms ↔
      rightLive j l.order ms = true ∧
      v<r.order ∧ ∀ m∈ms, l.order≤m → v≠m-l.order ∧ r.edge (m-l.order) v=false := by
  unfold rightBoard
  split
  · rename_i live
    simp only [mem_rest,Finset.mem_range,live,true_and,movesRight,List.mem_map,
      List.mem_filter,decide_eq_true_eq]
    refine and_congr_right fun _ => ⟨?_,?_⟩
    · intro h m hm hb
      exact h _ ⟨m,⟨hm,hb⟩,rfl⟩
    · rintro h _ ⟨m,⟨hm,hb⟩,rfl⟩
      exact h m hm hb
  · simp_all

private theorem combo_rest (j : Bool) (l r : Factor) (ms : List Nat) :
    rest (Factor.combine j l r).edge (Finset.range (l.order+r.order)) ms =
      leftBoard j l ms ∪ (rightBoard j l r ms).image (l.order+·) := by
  ext v
  simp only [mem_rest,Finset.mem_range,Finset.mem_union,Finset.mem_image,
    mem_leftBoard,mem_rightBoard,leftLive_spec,rightLive_spec]
  by_cases hv : v<l.order
  · simp only [hv,true_and,Factor.edge,ite_true]
    constructor
    · rintro ⟨_,keep⟩
      left
      refine ⟨?_,?_⟩
      · intro m hm hb
        simpa [show ¬m<l.order by omega] using (keep m hm).2
      · intro m hm hb
        simpa [hb] using keep m hm
    · rintro (⟨allow,keep⟩ | ⟨i,_,hi⟩)
      · refine ⟨by omega,?_⟩
        intro m hm
        by_cases hb : m<l.order
        · simpa [hb] using keep m hm hb
        · simp [hb,allow m hm (by omega),show v≠m by omega]
      · omega
  · simp only [hv,false_and,and_false,false_or,Factor.edge,ite_false]
    constructor
    · rintro ⟨hlt,keep⟩
      refine ⟨v-l.order,⟨?_,by omega,?_⟩,by omega⟩
      · intro m hm hb
        simpa [hb] using (keep m hm).2
      · intro m hm hb
        have h := keep m hm
        exact ⟨by omega,by simpa [show ¬ m<l.order by omega] using h.2⟩
    · rintro ⟨i,⟨allow,hi,keep⟩,rfl⟩
      refine ⟨by omega,?_⟩
      intro m hm
      by_cases hb : m<l.order
      · simp [hb,allow m hm hb,show l.order+i≠m by omega]
      · have h := keep m hm (by omega)
        rw [show l.order+i-l.order=i by omega]
        exact ⟨by omega,by simpa [hb] using h.2⟩

private theorem combo_separated (j : Bool) (l r : Factor) (ms : List Nat)
    (split : j=false ∨ ms≠[]) :
    Separated (Factor.combine j l r).edge (leftBoard j l ms) ((rightBoard j l r ms).image (l.order+·)) := by
  intro a ha v hv
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨left,lt,_⟩ := (mem_leftBoard _ _ _ _).mp ha
  obtain ⟨right,_,_⟩ := (mem_rightBoard _ _ _ _ _).mp hb
  have off : j=false := by
    rcases split with e|e
    · exact e
    · cases ms with
      | nil => exact (e rfl).elim
      | cons m ms =>
        by_cases hm : m<l.order
        · exact (rightLive_spec _ _ _).mp right m (by simp) hm
        · exact (leftLive_spec _ _ _).mp left m (by simp) (by omega)
  simp [Factor.edge,lt,show ¬ l.order+b<l.order by omega,off,show a≠l.order+b by omega]

private theorem combo_value (j : Bool) (l r : Factor) (ms : List Nat)
    (split : j=false ∨ ms≠[]) :
    value (Factor.combine j l r).edge
      (rest (Factor.combine j l r).edge (Finset.range (l.order+r.order)) ms) =
      value l.edge (leftBoard j l ms) ^^^ value r.edge (rightBoard j l r ms) := by
  rw [combo_rest,value_union _ _ _ (combo_separated j l r ms split)]
  have le : value (Factor.combine j l r).edge (leftBoard j l ms) =
      value l.edge (leftBoard j l ms) := by
    have e := value_image l.edge (Factor.combine j l r).edge id (leftBoard j l ms)
      (fun _ _ _ _ e => e) (by
        intro a ha b hb
        have al := ((mem_leftBoard _ _ _ _).mp ha).2.1
        have bl := ((mem_leftBoard _ _ _ _).mp hb).2.1
        simp [Factor.edge,al,bl])
    simpa using e
  have ri : value (Factor.combine j l r).edge ((rightBoard j l r ms).image (l.order+·)) =
      value r.edge (rightBoard j l r ms) :=
    value_image _ _ _ (rightBoard j l r ms) (fun _ _ _ _ e => by omega) (by
      intro a _ b _
      simp [Factor.edge,show ¬ l.order+a<l.order by omega,show ¬ l.order+b<l.order by omega])
  rw [le,ri]

private theorem join_first_left (l r : Factor) {v : Nat} (hv : v<l.order) :
    value (Factor.combine true l r).edge
      (drop (Factor.combine true l r).edge (Finset.range (l.order+r.order)) v) =
      value l.edge (drop l.edge (Finset.range l.order) v) := by
  rw [←rest_nil (Factor.combine true l r).edge (drop _ _ _),←rest_cons,
    combo_value _ _ _ _ (Or.inr (by simp))]
  simp [leftBoard,rightBoard,leftLive,rightLive,movesLeft,rest_cons,rest_nil,hv,
    show ¬ l.order≤v by omega,value_empty]

private theorem join_first_right (l r : Factor) (v : Nat) :
    value (Factor.combine true l r).edge
      (drop (Factor.combine true l r).edge (Finset.range (l.order+r.order)) (l.order+v)) =
      value r.edge (drop r.edge (Finset.range r.order) v) := by
  rw [←rest_nil (Factor.combine true l r).edge (drop _ _ _),←rest_cons,
    combo_value _ _ _ _ (Or.inr (by simp))]
  simp [leftBoard,rightBoard,leftLive,rightLive,movesRight,rest_cons,rest_nil,
    show ¬ l.order+v<l.order by omega,value_empty]

private theorem join_value (l r : Factor) :
    value (Factor.combine true l r).edge (Finset.range (l.order+r.order)) =
      mex (Modules.menu l.edge (Finset.range l.order) ∪ Modules.menu r.edge (Finset.range r.order)) := by
  rw [value_eq (Factor.combine true l r).edge]
  congr 1
  ext k
  simp only [Modules.menu,Finset.mem_image,Finset.mem_range,Finset.mem_union]
  constructor
  · rintro ⟨v,hv,he⟩
    by_cases h : v<l.order
    · exact Or.inl ⟨v,h,(join_first_left l r h).symm.trans he⟩
    · have ev : v=l.order+(v-l.order) := by omega
      rw [ev,join_first_right] at he
      exact Or.inr ⟨v-l.order,by omega,he⟩
  · rintro (⟨v,hv,he⟩|⟨v,hv,he⟩)
    · exact ⟨v,by omega,(join_first_left l r hv).trans he⟩
    · exact ⟨l.order+v,by omega,(join_first_right l r v).trans he⟩

private def literal (f : Factor) (ms : List Nat) : Nat :=
  value f.edge (rest f.edge (Finset.range f.order) ms)

private def evalPath (n : Nat) (ms : List Nat) : Nat :=
  if n≤75 then
    match ms with
    | [] => Path.expected n
    | [a] => if a<n then Path.expected (a-1) ^^^ Path.expected (n-a-2) else literal (.path n) ms
    | [a,b] =>
      if a<n ∧ b<n then
        let i := min a b
        let j := max a b
        Path.expected (i-1) ^^^ Path.expected (j-1-(i+2)) ^^^ Path.expected (n-(j+2))
      else literal (.path n) ms
    | _ => literal (.path n) ms
  else literal (.path n) ms

private theorem evalPath_sound (n : Nat) (ms : List Nat) :
    literal (.path n) ms = evalPath n ms := by
  unfold evalPath
  split
  · rename_i hn
    cases ms with
    | nil =>
      simp only [literal,Factor.order,rest_nil]
      change Path.score n = Path.expected n
      exact Path.score_eq_expected n hn
    | cons a ms =>
      cases ms with
      | nil =>
        change _ = if a<n then _ else _
        split
        · rename_i h
          show literal (.path n) [a] = _
          simp only [literal,Factor.order,rest_cons,rest_nil]
          change value Path.edge (drop Path.edge (Finset.range n) a) = _
          rw [Path.option_value h,Path.score_eq_expected _ (by omega),Path.score_eq_expected _ (by omega)]
        · rfl
      | cons b ms =>
        cases ms with
        | nil =>
          change _ = if a<n ∧ b<n then _ else _
          split
          · rename_i hab
            simp only [literal,Factor.order,rest_cons,rest_nil]
            change value Path.edge (drop Path.edge (drop Path.edge (Finset.range n) a) b) = _
            obtain ⟨ha,hb⟩ := hab
            by_cases ab : a≤b
            · rw [path_after_two n a b ha hb ab,Nat.min_eq_left ab,Nat.max_eq_right ab,
                Path.score_eq_expected _ (by omega),Path.score_eq_expected _ (by omega),
                Path.score_eq_expected _ (by omega)]
            · have commute : drop Path.edge (drop Path.edge (Finset.range n) a) b =
                  drop Path.edge (drop Path.edge (Finset.range n) b) a := by
                ext v
                simp only [drop,Finset.mem_filter]
                tauto
              have ba : b≤a := by omega
              rw [commute,path_after_two n b a hb ha ba,Nat.min_eq_right ba,Nat.max_eq_left ba,
                Path.score_eq_expected _ (by omega),Path.score_eq_expected _ (by omega),
                Path.score_eq_expected _ (by omega)]
          · rfl
        | cons => rfl
  · rfl

private def evalCycle (n : Nat) (ms : List Nat) : Nat :=
  if 3≤n ∧ n≤78 then
    match ms with
    | [] => if Path.expected (n-3)=0 then 1 else 0
    | [a] => if a<n then Path.expected (n-3) else literal (.cycle n) ms
    | [a,b] =>
      if a<n ∧ b<n ∧ b≠a ∧ cycleEdge n a b=false then
        let i := if a+2≤b then b-(a+2) else n+b-(a+2)
        Path.expected (i-1) ^^^ Path.expected (n-3-i-2)
      else literal (.cycle n) ms
    | _ => literal (.cycle n) ms
  else literal (.cycle n) ms

private theorem evalCycle_sound (n : Nat) (ms : List Nat) :
    literal (.cycle n) ms = evalCycle n ms := by
  unfold evalCycle
  split
  · rename_i hn
    cases ms with
    | nil =>
      simp only [literal,Factor.order,rest_nil]
      change value (cycleEdge n) (Finset.range n) = _
      rw [cycle_value n hn.1,Path.score_eq_expected _ (by omega)]
    | cons a ms =>
      cases ms with
      | nil =>
        change _ = if a<n then _ else _
        split
        · rename_i ha
          simp only [literal,Factor.order,rest_cons,rest_nil]
          change value (cycleEdge n) (drop (cycleEdge n) (Finset.range n) a) = _
          rw [cycle_after n a hn.1 ha,Path.score_eq_expected _ (by omega)]
        · rfl
      | cons b ms =>
        cases ms with
        | nil =>
          change _ = if a<n ∧ b<n ∧ b≠a ∧ cycleEdge n a b=false then _ else _
          split
          · rename_i hab
            have live : b ∈ drop (cycleEdge n) (Finset.range n) a := by
              simp only [drop,Finset.mem_filter,Finset.mem_range]
              exact hab.2
            have eq := cycle_after_two n a b hn.1 hab.1 live
            simp only [literal,Factor.order,rest_cons,rest_nil]
            change value (cycleEdge n) (drop (cycleEdge n) (drop (cycleEdge n) (Finset.range n) a) b) = _
            rw [eq]
            have ib := cycle_index_lt n a b hn.1 hab.1 live
            rw [Path.score_eq_expected _ (by omega),Path.score_eq_expected _ (by omega)]
          · rfl
        | cons => rfl
  · rfl

/-- Factor by factor score. The path table handles the large factors of the witness. -/
private def fast : Factor → List Nat → Nat
  | .path n, ms => evalPath n ms
  | .cycle n, ms => evalCycle n ms
  | .bits n mask, ms => literal (.bits n mask) ms
  | .combine j l r, ms =>
    if j && ms.isEmpty then
      mex (((Finset.range l.order).image (fun m => fast l [m])) ∪
        ((Finset.range r.order).image (fun m => fast r [m])))
    else
      (if leftLive j l.order ms then fast l (movesLeft l.order ms) else 0) ^^^
      (if rightLive j l.order ms then fast r (movesRight l.order ms) else 0)

private theorem fast_sound (f : Factor) (ms : List Nat) : literal f ms = fast f ms := by
  induction f generalizing ms with
  | bits => rfl
  | path n => exact evalPath_sound n ms
  | cycle n => exact evalCycle_sound n ms
  | combine j l r ihl ihr =>
    rw [fast]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      obtain ⟨rfl, hnil⟩ := h
      cases ms with
      | cons => simp at hnil
      | nil =>
        simp only [literal,Factor.order,rest_nil,join_value,Modules.menu]
        apply congrArg mex
        congr 1
        · apply Finset.image_congr
          intro v _
          simpa only [literal,rest_cons,rest_nil] using ihl [v]
        · apply Finset.image_congr
          intro v _
          simpa only [literal,rest_cons,rest_nil] using ihr [v]
    · rename_i h
      have hsep : j=false ∨ ms≠[] := by
        cases j <;> cases ms <;> simp_all
      simp only [literal,Factor.order,combo_value _ _ _ _ hsep]
      congr 1
      · unfold leftBoard
        split
        · exact ihl _
        · exact value_empty _
      · unfold rightBoard
        split
        · exact ihr _
        · exact value_empty _

private def history (h : Fin 8) : List Nat :=
  if h.val = 0 then [] else [(marks ⟨h.val-1, by omega⟩).val]

private theorem rest_append (E : Nat → Nat → Bool) (s : Finset Nat) (ms : List Nat) (i : Nat) :
    rest E s (ms++[i]) = drop E (rest E s ms) i := by
  ext v
  simp only [mem_rest,drop,Finset.mem_filter,List.mem_append,List.mem_singleton]
  constructor
  · rintro ⟨hv,h⟩
    exact ⟨⟨hv,fun m hm => h m (Or.inl hm)⟩,h i (Or.inr rfl)⟩
  · rintro ⟨⟨hv,h⟩,hi⟩
    refine ⟨hv,?_⟩
    rintro m (hm|rfl)
    · exact h m hm
    · exact hi

private theorem labels : (Finset.univ : Finset (Fin 279)).image Fin.val = Finset.range 279 := by
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_range]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ i.isLt,fun h => ⟨⟨v,h⟩,rfl⟩⟩

private theorem order_core : joinedCore.order = 279 := by decide +kernel

private theorem board_labels (h : Fin 8) :
    (coreBoard h).image Fin.val = rest joinedCore.edge (Finset.range 279) (history h) := by
  unfold coreBoard history
  split
  · rw [labels,rest_nil]
  · rw [rest_cons,rest_nil,←labels]
    exact (drop_image coreEdge joinedCore.edge _ Fin.val
      (fun _ _ _ _ eq => Fin.ext eq) (fun _ _ _ _ => rfl) (Finset.mem_univ _)).symm

private theorem exact_move (h : Fin 8) (v : Fin 279) (hv : v ∈ coreBoard h) :
    value coreEdge (drop coreEdge (coreBoard h) v) =
      fast joinedCore (history h ++ [v.val]) := by
  have inj : Set.InjOn Fin.val (↑(coreBoard h) : Set (Fin 279)) :=
    fun _ _ _ _ e => Fin.ext e
  have e := value_image coreEdge joinedCore.edge Fin.val (drop coreEdge (coreBoard h) v)
    (fun _ _ _ _ e => Fin.ext e) (fun _ _ _ _ => rfl)
  rw [←drop_image coreEdge joinedCore.edge _ Fin.val inj (fun _ _ _ _ => rfl) hv,
    board_labels,←rest_append,congrArg Finset.range order_core.symm] at e
  exact e.symm.trans (fast_sound _ _)

private def markLabels : List Nat := [0,5,30,55,101,177,198]

private theorem marked_labels (v : Fin 279) : v ∈ marked ↔ v.val ∈ markLabels := by
  have e : ((Finset.univ : Finset (Fin 7)).image fun i => (marks i).val) = markLabels.toFinset := by
    decide +kernel
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    have t : (marks i).val ∈ (Finset.univ : Finset (Fin 7)).image (fun i => (marks i).val) :=
      Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    simpa only [e,List.mem_toFinset] using t
  · intro hv
    have t : v.val ∈ markLabels.toFinset := List.mem_toFinset.mpr hv
    rw [←e] at t
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp t
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,Fin.ext eq⟩

private def validNear (h : Fin 8) (i : Nat) : Bool :=
  !(markLabels.contains i) &&
    (history h).all (fun m => decide (i≠m ∧ joinedCore.edge m i=false))

private theorem near_labels (h : Fin 8) (v : Fin 279) :
    v ∈ nearBoard h ↔ validNear h v.val = true := by
  have live : v ∈ coreBoard h ↔ v.val ∈ (coreBoard h).image Fin.val := by
    simp only [Finset.mem_image]
    constructor
    · exact fun hv => ⟨v,hv,rfl⟩
    · rintro ⟨u,hu,e⟩
      have s : u=v := Fin.ext e
      exact s ▸ hu
  simp only [nearBoard,Finset.mem_sdiff,marked_labels,live,board_labels,mem_rest,Finset.mem_range,
    validNear,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,List.contains_eq_mem,
    ←decide_not,v.isLt,true_and]
  tauto

private def computedValues (h : Fin 8) : List Nat :=
  ((List.range 279).filter (validNear h)).map fun v => fast joinedCore (history h ++ [v])

private def flags : List Nat → Nat
  | [] => 0
  | k::ks => (2^k) ||| flags ks

private theorem flags_mem (l : List Nat) (k : Nat) : (flags l).testBit k = true ↔ k∈l := by
  induction l with
  | nil => simp [flags]
  | cons a l ih =>
    simp only [flags,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,
      decide_eq_true_eq,ih,List.mem_cons]
    exact or_congr eq_comm Iff.rfl

private theorem mask_mem (h : Fin 8) (k : Nat) : (mask h).testBit k = true ↔ k∈menu h := by
  have bounds : ∀ h : Fin 8, mask h < 2^12 := by decide +kernel
  simp only [menu,Finset.mem_filter,Finset.mem_range]
  refine ⟨fun hb => ⟨?_,hb⟩,And.right⟩
  by_contra hn
  have hlt : mask h < 2^k := lt_of_lt_of_le (bounds h) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.testBit_lt_two_pow hlt] at hb
  contradiction

private def block (h : Fin 8) (start len : Nat) : Nat :=
  flags (((List.range' start len).filter (validNear h)).map
    (fun v => fast joinedCore (history h ++ [v])))

private theorem flags_append (xs ys : List Nat) : flags (xs++ys) = flags xs ||| flags ys := by
  induction xs with
  | nil => simp [flags]
  | cons x xs ih => simp [flags,ih,Nat.or_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem parent_block_1 : block 0 0 5 = 11 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem child_block_1 : block 1 0 5 = 7 := by decide +kernel

set_option maxRecDepth 5000 in
private theorem child_range_1 :
    (List.range 279).filter (validNear 1) = (List.range' 0 5).filter (validNear 1) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem parent_block_2 : block 0 5 25 = 15 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem child_block_2 : block 2 5 25 = 45 := by decide +kernel

set_option maxRecDepth 5000 in
private theorem child_range_2 :
    (List.range 279).filter (validNear 2) = (List.range' 5 25).filter (validNear 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem parent_block_3 : block 0 30 25 = 15 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem child_block_3 : block 3 30 25 = 71 := by decide +kernel

set_option maxRecDepth 5000 in
private theorem child_range_3 :
    (List.range 279).filter (validNear 3) = (List.range' 30 25).filter (validNear 3) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem parent_block_4 : block 0 55 46 = 15 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem child_block_4 : block 4 55 46 = 132 := by decide +kernel

set_option maxRecDepth 5000 in
private theorem child_range_4 :
    (List.range 279).filter (validNear 4) = (List.range' 55 46).filter (validNear 4) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem parent_block_5 : block 0 101 76 = 11 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem child_block_5 : block 5 101 76 = 227 := by decide +kernel

set_option maxRecDepth 5000 in
private theorem child_range_5 :
    (List.range 279).filter (validNear 5) = (List.range' 101 76).filter (validNear 5) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem parent_block_6 : block 0 177 21 = 15 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem child_block_6 : block 6 177 21 = 247 := by decide +kernel

set_option maxRecDepth 5000 in
private theorem child_range_6 :
    (List.range 279).filter (validNear 6) = (List.range' 177 21).filter (validNear 6) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem parent_block_7 : block 0 198 81 = 11 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem child_block_7 : block 7 198 81 = 1271 := by decide +kernel

set_option maxRecDepth 5000 in
private theorem child_range_7 :
    (List.range 279).filter (validNear 7) = (List.range' 198 81).filter (validNear 7) := by
  decide +kernel

set_option maxRecDepth 5000 in
private theorem parent_range :
    List.range 279 =
      List.range' 0 5 ++ List.range' 5 25 ++ List.range' 30 25 ++ List.range' 55 46 ++
      List.range' 101 76 ++ List.range' 177 21 ++ List.range' 198 81 := by
  decide +kernel

private theorem certified (h : Fin 8) : flags (computedValues h) = mask h := by
  obtain ⟨h, hh⟩ := h
  have e : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 := by omega
  rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change flags (computedValues 0) = mask 0
    unfold computedValues
    rw [parent_range]
    simp only [List.filter_append,List.map_append,flags_append]
    change block 0 0 5 ||| (block 0 5 25 ||| (block 0 30 25 ||| (block 0 55 46 |||
      (block 0 101 76 ||| (block 0 177 21 ||| block 0 198 81))))) = 15
    simpa only [parent_block_1,parent_block_2,parent_block_3,parent_block_4,parent_block_5,parent_block_6,parent_block_7] using
      (show 11 ||| (15 ||| (15 ||| (15 ||| (11 ||| (15 ||| 11))))) = 15 by decide)
  · change flags (computedValues 1) = mask 1
    rw [computedValues,child_range_1]
    exact child_block_1
  · change flags (computedValues 2) = mask 2
    rw [computedValues,child_range_2]
    exact child_block_2
  · change flags (computedValues 3) = mask 3
    rw [computedValues,child_range_3]
    exact child_block_3
  · change flags (computedValues 4) = mask 4
    rw [computedValues,child_range_4]
    exact child_block_4
  · change flags (computedValues 5) = mask 5
    rw [computedValues,child_range_5]
    exact child_block_5
  · change flags (computedValues 6) = mask 6
    rw [computedValues,child_range_6]
    exact child_block_6
  · change flags (computedValues 7) = mask 7
    rw [computedValues,child_range_7]
    exact child_block_7

private theorem verified_members (h : Fin 8) (k : Nat) : k∈computedValues h ↔ k∈menu h := by
  rw [←flags_mem, certified, mask_mem]

theorem near_menu (h : Fin 8) :
    (nearBoard h).image (fun v => value coreEdge (drop coreEdge (coreBoard h) v)) = menu h := by
  ext k
  rw [←verified_members h k]
  simp only [Finset.mem_image,computedValues,List.mem_map,List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨v.val,⟨v.isLt,(near_labels h v).mp hv⟩, (exact_move h v (Finset.mem_sdiff.mp hv).1).symm⟩
  · rintro ⟨v,⟨hlt,hv⟩,rfl⟩
    let w : Fin 279 := ⟨v,hlt⟩
    have hm : w ∈ nearBoard h := (near_labels h w).mpr hv
    exact ⟨w,hm,exact_move h w (Finset.mem_sdiff.mp hm).1⟩
theorem marks_joined (a b : Fin 7) (h : marks a ≠ marks b) : coreEdge (marks a) (marks b) = true := by
  have e : ∀ a b : Fin 7, marks a ≠ marks b → coreEdge (marks a) (marks b) = true := by
    decide +kernel
  exact e a b h

theorem far_eq (h : Fin 8) : farBoard h = if h.val=0 then marked else ∅ := by
  unfold farBoard coreBoard
  split
  · simp
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).2
    obtain ⟨_,hn,e⟩ := Finset.mem_filter.mp (Finset.mem_inter.mp hv).1
    rw [marks_joined _ _ (Ne.symm hn)] at e
    contradiction


private theorem mex_menu (h : Fin 8) : mex (menu h) = erased h := by
  have cert : ∀ h : Fin 8, mex (menu h) = erased h := by decide +kernel
  exact cert h

private theorem core_mex (h : Fin 8) :
    value coreEdge (coreBoard h) =
      mex (menu h ∪ ((farBoard h).image fun v => value coreEdge (drop coreEdge (coreBoard h) v))) := by
  have eq : coreBoard h = nearBoard h ∪ farBoard h := by
    ext v
    simp only [nearBoard,farBoard,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  rw [value_eq coreEdge (coreBoard h)]
  conv_lhs => arg 1; arg 2; rw [eq]
  rw [Finset.image_union,near_menu]

private theorem child_erased (h : Fin 8) (hh : h.val ≠ 0) :
    value coreEdge (coreBoard h) = erased h := by
  rw [core_mex,far_eq,ite_eq_right hh,Finset.image_empty,Finset.union_empty,mex_menu]

theorem erased_value (h : Fin 8) : value coreEdge (coreBoard h) = erased h := by
  by_cases hz : h.val=0
  · have h0 : h=0 := Fin.ext hz
    subst h
    have vals : ∀ i : Fin 7, erased ⟨i.val+1,by omega⟩ ∈ menu 0 := by decide +kernel
    have incl : ((farBoard 0).image fun v => value coreEdge (drop coreEdge (coreBoard 0) v)) ⊆ menu 0 := by
      intro k hk
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
      have hm : v ∈ marked := (Finset.mem_inter.mp hv).2
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
      let child : Fin 8 := ⟨i.val+1,by omega⟩
      have hc : child.val≠0 := by simp [child]
      have cb : coreBoard child = drop coreEdge (coreBoard 0) (marks i) := by
        have parent : coreBoard (0 : Fin 8) = Finset.univ := rfl
        rw [parent,coreBoard,dite_eq_right hc]
        have idx : (⟨child.val-1,by have := child.isLt; omega⟩ : Fin 7) = i := by
          exact Fin.ext (Nat.add_sub_cancel _ _)
        rw [idx]
      rw [←cb,child_erased child hc]
      exact vals i
    rw [core_mex,Finset.union_eq_left.mpr incl,mex_menu]
  · exact child_erased h hz

theorem hub_value (h : Fin 8) :
    value coreEdge (farBoard h) = if h.val=0 then 1 else 0 := by
  rw [far_eq]
  split
  · have empty (v : Fin 279) (hv : v∈marked) : drop coreEdge marked v=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hm,hn,he⟩ := Finset.mem_filter.mp hw
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hm
      rw [marks_joined _ _ hn.symm] at he
      contradiction
    obtain ⟨ha,hb⟩ := value_spec coreEdge marked
    apply mex_unique ⟨ha,hb⟩
    refine ⟨?_,?_⟩
    · rintro ⟨v,hv,e⟩
      rw [empty v hv,value_empty] at e
      exact Nat.zero_ne_one e
    · intro k hk
      have e : k=0 := by omega
      subst k
      have mem : marks 0 ∈ marked := Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
      exact ⟨marks 0,mem,(congrArg (value coreEdge) (empty _ mem)).trans (value_empty _)⟩
  · exact value_empty _

#print axioms near_menu
#print axioms erased_value
#print axioms hub_value

end KaylesRays.PeriodFourMenus
