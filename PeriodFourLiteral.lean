module

public import PeriodFourTarget
public import PeriodFourMenus
public import MixedPaths
public import BoardMap
public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace KaylesRays.PeriodFourLiteral
open LiteralKayles PeriodFourGraph
open MixedPaths (Site siteEdge mixed pathPrefix)
open PeriodFourMenus (coreEdge marks marked coreBoard nearBoard farBoard)

/-- The old labels below 280 are exactly the core and its hub. -/
def coreLabel : Option (Fin 279) → Fin 291
  | none => hub
  | some v => ⟨v.val, by omega⟩

def coreAdj (a b : Option (Fin 279)) : Bool :=
  hostEdge (coreLabel a) (coreLabel b)

@[simp] theorem coreAdj_some (a b : Fin 279) :
    coreAdj (some a) (some b) = coreEdge a b := by
  simp [coreAdj,coreLabel,hostEdge,coreEdge,a.isLt,b.isLt]

def isMark (v : Fin 279) : Prop := v.val ∈ [0,5,30,55,101,177,198]

instance decIsMark (v : Fin 279) : Decidable (isMark v) :=
  inferInstanceAs (Decidable (v.val ∈ [0,5,30,55,101,177,198]))

private theorem coreAdj_to_hub (a : Fin 279) :
    coreAdj (some a) none = decide (¬isMark a) := by
  have ha : a.val < 279 := a.isLt
  have hn : a.val ≠ 279 := by omega
  have h282 : ¬282≤a.val := by omega
  have h285 : ¬285≤a.val := by omega
  have h288 : ¬288≤a.val := by omega
  simp [coreAdj,coreLabel,hostEdge,hub,hn,h282,h285,h288]
  change ((decide ((a.val < 279 ∧ ¬isMark a) ∨ a.val∈[280,281,282,285,288])) : Bool) = _
  have hrest : a.val ∉ [280,281,282,285,288] := by simp; omega
  simp [ha,hrest]

private theorem coreAdj_from_hub (a : Fin 279) :
    coreAdj none (some a) = decide (¬isMark a) := by
  have ha : a.val < 279 := a.isLt
  have hn : a.val ≠ 279 := by omega
  have h282 : ¬282≤a.val := by omega
  have h285 : ¬285≤a.val := by omega
  have h288 : ¬288≤a.val := by omega
  simp [coreAdj,coreLabel,hostEdge,hub,hn,h282,h285,h288]
  change ((decide ((a.val < 279 ∧ ¬isMark a) ∨ a.val∈[280,281,282,285,288])) : Bool) = _
  have hrest : a.val ∉ [280,281,282,285,288] := by simp; omega
  simp [ha,hrest]

@[simp] theorem coreAdj_self_hub : coreAdj none none = false := by decide +kernel

private theorem mark_index : ∀ i : Fin 7,
    ([0,5,30,55,101,177,198] : List Nat)[i.val]? = some (marks i).val := by
  decide +kernel

private theorem mark_eq (a : Fin 279) : isMark a ↔ a ∈ marked := by
  constructor
  · intro ha
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp ha
    let j : Fin 7 := ⟨i,hi⟩
    refine Finset.mem_image.mpr ⟨j,Finset.mem_univ _,Fin.ext ?_⟩
    have he := mark_index j
    change ([0,5,30,55,101,177,198] : List Nat)[i]? = some (marks j).val at he
    rw [getElem?_pos ([0,5,30,55,101,177,198] : List Nat) i hi,hval] at he
    exact (Option.some.inj he).symm
  · intro ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact List.mem_of_getElem? (mark_index i)

theorem coreAdj_to_hub_marked (a : Fin 279) :
    coreAdj (some a) none = decide (a∉marked) := by
  exact (coreAdj_to_hub a).trans (decide_eq_decide.mpr (not_congr (mark_eq a)))

theorem coreAdj_from_hub_marked (a : Fin 279) :
    coreAdj none (some a) = decide (a∉marked) := by
  exact (coreAdj_from_hub a).trans (decide_eq_decide.mpr (not_congr (mark_eq a)))

/-- Each phase contains the hub and exactly the indicated live core vertices. -/
def hostBoard (h : Fin 8) : Finset (Option (Fin 279)) :=
  insert none ((coreBoard h).image some)

@[simp] theorem hostBoard_none_mem (h : Fin 8) : none∈hostBoard h := by simp [hostBoard]

@[simp] theorem hostBoard_some_mem (h : Fin 8) (v : Fin 279) :
    some v∈hostBoard h ↔ v∈coreBoard h := by simp [hostBoard]

@[simp] theorem hostBoard_erase (h : Fin 8) :
    (hostBoard h).erase none = (coreBoard h).image some := by
  simp [hostBoard]

theorem hostBoard_zero : hostBoard 0 = Finset.univ := by
  ext a
  cases a <;> simp [hostBoard,coreBoard]

theorem hostBoard_hub (h : Fin 8) :
    drop coreAdj (hostBoard h) none = (farBoard h).image some := by
  ext a
  cases a <;> simp [drop,hostBoard,farBoard,coreAdj_from_hub_marked]

theorem hostBoard_near (h : Fin 8) {v : Fin 279} (hv : v∈nearBoard h) :
    drop coreAdj (hostBoard h) (some v) = (drop coreEdge (coreBoard h) v).image some := by
  have hm := (Finset.mem_sdiff.mp hv).2
  ext a
  cases a <;> simp [drop,hostBoard,coreAdj_to_hub_marked,hm]

theorem hostBoard_quiet (i : Fin 7) :
    drop coreAdj (hostBoard 0) (some (marks i)) = hostBoard ⟨i.val+1,by omega⟩ := by
  have hm : marks i∈marked := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hc : coreBoard ⟨i.val+1,by omega⟩ = drop coreEdge Finset.univ (marks i) := by
    simp [coreBoard]
  have hz : coreBoard (0 : Fin 8) = Finset.univ := rfl
  ext a
  cases a <;> simp [drop,hostBoard,coreAdj_to_hub_marked,hm,hc,hz]

theorem core_image_value (s : Finset (Fin 279)) :
    value coreAdj (s.image some) = value coreEdge s := by
  refine value_image coreEdge coreAdj some s ?_ (fun a _ b _ => coreAdj_some a b)
  intro a _ b _ h
  exact Option.some.inj h

def fixedOld (i : Fin 11) : Fin 291 := ⟨280+i.val, by omega⟩

/-- Two length-one arms and three length-three arms, named in host order. -/
def fixedSite (i : Fin 11) : Nat × Fin 5 :=
  if i.val<2 then (i.val,0)
  else ((i.val-2)/3+2,⟨(i.val-2)%3,by omega⟩)

def oldSite (i : Fin 291) : Site (Option (Fin 279)) :=
  if h : i.val < 279 then .inl (some ⟨i.val,h⟩)
  else if h' : i.val = 279 then .inl none
  else .inr (fixedSite ⟨i.val-280, by omega⟩)

def vertexSite : Vertex → Site (Option (Fin 279))
  | .old i => oldSite i
  | .ray n i => .inr (n+5,i)

@[simp] private theorem oldSite_core (a : Option (Fin 279)) :
    oldSite (coreLabel a) = .inl a := by
  cases a with
  | none => rfl
  | some a => simp [oldSite,coreLabel,a.isLt]

@[simp] private theorem oldSite_fixed (i : Fin 11) :
    oldSite (fixedOld i) = .inr (fixedSite i) := by
  have hn : ¬280+i.val<279 := by omega
  have hn' : 280+i.val≠279 := by omega
  simp [oldSite,fixedOld,hn,hn']

private theorem split_old (i : Fin 291) :
    (∃ a, i = coreLabel a) ∨ (∃ a, i = fixedOld a) := by
  by_cases h : i.val<279
  · exact Or.inl ⟨some ⟨i.val,h⟩,Fin.ext rfl⟩
  by_cases h' : i.val=279
  · exact Or.inl ⟨none,Fin.ext h'⟩
  exact Or.inr ⟨⟨i.val-280,by omega⟩,Fin.ext (by change i.val=280+(i.val-280); omega)⟩

private theorem fixed_index : ∀ i : Fin 11, (fixedSite i).1 < 5 := by decide +kernel

private theorem fixed_inj : ∀ a b : Fin 11, fixedSite a = fixedSite b → a=b := by
  decide +kernel

theorem vertexSite_inj : Function.Injective vertexSite := by
  intro a b h
  cases a with
  | old a =>
    rcases split_old a with ⟨a,rfl⟩|⟨a,rfl⟩ <;>
      cases b with
      | old b =>
        rcases split_old b with ⟨b,rfl⟩|⟨b,rfl⟩
        · simp only [vertexSite,oldSite_core,oldSite_fixed,Sum.inl.injEq] at h
          first | subst b; rfl | contradiction
        · simp only [vertexSite,oldSite_core,oldSite_fixed,Sum.inr.injEq] at h
          first | exact congrArg (Vertex.old ∘ fixedOld) (fixed_inj _ _ h) | contradiction
      | ray n i =>
        simp only [vertexSite,oldSite_core,oldSite_fixed,Sum.inr.injEq] at h
        first | contradiction
              | have e := congrArg Prod.fst h
                have h' := fixed_index a
                simp at e
                omega
  | ray n i =>
    cases b with
    | old b =>
      rcases split_old b with ⟨b,rfl⟩|⟨b,rfl⟩
      · simp [vertexSite] at h
      · simp only [vertexSite,oldSite_fixed,Sum.inr.injEq] at h
        have e := congrArg Prod.fst h
        have h' := fixed_index b
        simp at e
        omega
    | ray m j => simpa [vertexSite,Prod.ext_iff] using h

def vertexEmbedding : Vertex ↪ Site (Option (Fin 279)) :=
  ⟨vertexSite,vertexSite_inj⟩

private theorem coreLabel_hub (a : Option (Fin 279)) : coreLabel a=hub ↔ a=none := by
  cases a with
  | none => simp [coreLabel]
  | some a =>
    have h : a.val ≠ 279 := by have := a.isLt; omega
    simp [coreLabel,hub,Fin.ext_iff,h]

private theorem fixedOld_ne_hub (i : Fin 11) : fixedOld i ≠ hub := by
  simp [fixedOld,hub,Fin.ext_iff]
  omega

private theorem fixed_hub_edges : ∀ a : Fin 11,
    siteEdge coreAdj none (.inl none) (.inr (fixedSite a)) = hostEdge hub (fixedOld a) ∧
    siteEdge coreAdj none (.inr (fixedSite a)) (.inl none) = hostEdge (fixedOld a) hub := by
  decide +kernel

private theorem fixed_edges : ∀ a b : Fin 11,
    siteEdge coreAdj none (.inr (fixedSite a)) (.inr (fixedSite b)) =
      hostEdge (fixedOld a) (fixedOld b) := by
  decide +kernel

private theorem fixed_core_edges (a : Fin 279) (b : Fin 11) :
    hostEdge (coreLabel (some a)) (fixedOld b) = false ∧
      hostEdge (fixedOld b) (coreLabel (some a)) = false := by
  have ha : a.val ≠ 279 := by have := a.isLt; omega
  have hb : 280+b.val ≠ 279 := by omega
  have hb' : ¬280+b.val < 279 := by omega
  have h282 : ¬282≤a.val := by have := a.isLt; omega
  have h285 : ¬285≤a.val := by have := a.isLt; omega
  have h288 : ¬288≤a.val := by have := a.isLt; omega
  simp [hostEdge,coreLabel,fixedOld,ha,hb,hb',h282,h285,h288]

private theorem core_fixed_edges (a : Option (Fin 279)) (b : Fin 11) :
    siteEdge coreAdj none (.inl a) (.inr (fixedSite b)) = hostEdge (coreLabel a) (fixedOld b) ∧
      siteEdge coreAdj none (.inr (fixedSite b)) (.inl a) = hostEdge (fixedOld b) (coreLabel a) := by
  cases a with
  | none => exact fixed_hub_edges b
  | some a =>
    have h := fixed_core_edges a b
    rcases hf : fixedSite b with ⟨k,i⟩
    simp [siteEdge,h.1,h.2]

private theorem vertexSite_edge (a b : Vertex) :
    siteEdge coreAdj none (vertexEmbedding a) (vertexEmbedding b) = edge a b := by
  change siteEdge coreAdj none (vertexSite a) (vertexSite b) = edge a b
  cases a with
  | old a =>
    cases b with
    | old b =>
      rcases split_old a with ⟨a,rfl⟩|⟨a,rfl⟩ <;>
        rcases split_old b with ⟨b,rfl⟩|⟨b,rfl⟩ <;>
        simp only [vertexSite,oldSite_core,oldSite_fixed,edge]
      · rfl
      · exact (core_fixed_edges a b).1
      · exact (core_fixed_edges b a).2
      · exact fixed_edges a b
    | ray n i =>
      rcases split_old a with ⟨a,rfl⟩|⟨a,rfl⟩
      · simp [vertexSite,siteEdge,edge,coreLabel_hub]
      · rcases hf : fixedSite a with ⟨k,j⟩
        have hk : k<5 := by simpa [hf] using fixed_index a
        have hne : k≠n+5 := by omega
        simp [vertexSite,hf,siteEdge,edge,hne,fixedOld_ne_hub]
  | ray n i =>
    cases b with
    | old b =>
      rcases split_old b with ⟨b,rfl⟩|⟨b,rfl⟩
      · simp [vertexSite,siteEdge,edge,coreLabel_hub]
      · rcases hf : fixedSite b with ⟨k,j⟩
        have hk : k<5 := by simpa [hf] using fixed_index b
        have hne : n+5≠k := by omega
        simp [vertexSite,hf,siteEdge,edge,hne,fixedOld_ne_hub]
    | ray m j => simp [vertexSite,siteEdge,edge,FiveMoves.rayEdge]

def canonicalIds (x : Nat) : Finset Nat := Finset.range (x+5)

def canonicalKind (n : Nat) := if n<2 then 1 else if n<5 then 3 else 5

def canonicalArms (n : Nat) : Finset (Fin 5) :=
  pathPrefix (canonicalKind n)

theorem canonical_live (x : Nat) : ∀ n∈canonicalIds x,
    canonicalKind n=5 ∨ canonicalKind n=3 ∨ canonicalKind n=1 := by
  intro n _
  unfold canonicalKind
  split_ifs <;> simp

theorem canonical_counts (x : Nat) :
    ((canonicalIds x).filter fun n => canonicalKind n=5).card=x ∧
    ((canonicalIds x).filter fun n => canonicalKind n=3).card=3 ∧
    ((canonicalIds x).filter fun n => canonicalKind n=1).card=2 := by
  have five : (canonicalIds x).filter (fun n => canonicalKind n=5) = Finset.Ico 5 (x+5) := by
    ext n
    rw [Finset.mem_filter,canonicalIds,Finset.mem_range,Finset.mem_Ico]
    unfold canonicalKind
    split_ifs <;> omega
  have three : (canonicalIds x).filter (fun n => canonicalKind n=3) = Finset.Ico 2 5 := by
    ext n
    rw [Finset.mem_filter,canonicalIds,Finset.mem_range,Finset.mem_Ico]
    unfold canonicalKind
    split_ifs <;> omega
  have one : (canonicalIds x).filter (fun n => canonicalKind n=1) = Finset.Ico 0 2 := by
    ext n
    rw [Finset.mem_filter,canonicalIds,Finset.mem_range,Finset.mem_Ico]
    unfold canonicalKind
    split_ifs <;> omega
  simp [five,three,one]

private theorem fixed_live : ∀ a : Fin 11, (fixedSite a).2 ∈ canonicalArms (fixedSite a).1 := by
  decide +kernel

private theorem fixed_complete : ∀ (n : Fin 5) (i : Fin 5), i∈canonicalArms n.val →
    ∃ a : Fin 11, fixedSite a = (n.val,i) := by
  decide +kernel

private theorem mem_board_old (x : Nat) (a : Fin 291) : Vertex.old a ∈ board x := by
  simp [board]

private theorem mem_board_ray (x n : Nat) (i : Fin 5) : Vertex.ray n i ∈ board x ↔ n<x := by
  simp [board]

private theorem vertexEmbedding_board (x : Nat) :
    (board x).map vertexEmbedding = mixed Finset.univ (canonicalIds x) canonicalArms := by
  ext z
  constructor
  · rintro hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hz
    change vertexSite v ∈ _
    cases v with
    | old v =>
      rcases split_old v with ⟨v,rfl⟩|⟨v,rfl⟩
      · simp [vertexSite]
      · have hm : (fixedSite v).1 < x+5 := by have := fixed_index v; omega
        rcases hf : fixedSite v with ⟨n,i⟩
        have hn : n < x+5 := by simpa [hf] using hm
        have hi : i∈canonicalArms n := by simpa [hf] using fixed_live v
        simp [vertexSite,hf,canonicalIds,hn,hi]
    | ray n i =>
      have hn : n<x := (mem_board_ray x n i).mp hv
      have hi := i.isLt
      have hn₂ : ¬n+5<2 := by omega
      have hn₅ : ¬n+5<5 := by omega
      simp [vertexSite,canonicalIds,canonicalArms,canonicalKind,hn,hi,hn₂,hn₅]
  · intro hz
    rcases z with (a|⟨n,i⟩)
    · exact Finset.mem_map.mpr ⟨.old (coreLabel a), mem_board_old x _, by simp [vertexEmbedding,vertexSite]⟩
    · have hnhi : n<x+5 ∧ i∈canonicalArms n := by
        simpa [canonicalIds] using hz
      by_cases hn : n<5
      · obtain ⟨a,ha⟩ := fixed_complete ⟨n,hn⟩ i hnhi.2
        exact Finset.mem_map.mpr
          ⟨.old (fixedOld a),mem_board_old x _,by simp [vertexEmbedding,vertexSite,ha]⟩
      · have hs : n-5<x := by have := hnhi.1; omega
        have hsum : n-5+5=n := by omega
        exact Finset.mem_map.mpr
          ⟨.ray (n-5) i,(mem_board_ray x _ _).mpr hs,by simp [vertexEmbedding,vertexSite,hsum]⟩

/-- The literal host with x new rays is the mixed board with two leaves,
three shorter branches and x length-five branches. -/
theorem score_eq_mixed (x : Nat) :
    PeriodFourGraph.score x =
      MixedPaths.score coreAdj none Finset.univ (canonicalIds x) canonicalArms := by
  unfold PeriodFourGraph.score MixedPaths.score
  rw [← vertexEmbedding_board x]
  exact (value_map edge (siteEdge coreAdj none) vertexEmbedding vertexSite_edge (board x)).symm

end KaylesRays.PeriodFourLiteral

#print axioms KaylesRays.PeriodFourLiteral.score_eq_mixed
