module

public import GrabbingGraph
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

namespace GraphGrabbing
open Finset

/-- A side of the cut at b, with no exit except through b. -/
private def Side (E : Edge) (S : Vertices) (b : ℕ) (W : Vertices) :=
  ∀ u∈W, ∀ v∈S, v∉W → E u v → v=b

private theorem cut_side {E : Edge} (sym : Undirected E) {S : Vertices} {x b : ℕ}
    (hb : b∈S) (bad : ¬Legal E S b) :
    ∃ W⊆S.erase b, W.Nonempty ∧ x∉W ∧ Side E S b W := by
  classical
  have fail : ¬Connected E (S.erase b) := fun c => bad ⟨hb,c⟩
  unfold Connected at fail
  push Not at fail
  obtain ⟨A,sub,an,bn,sep⟩ := fail
  by_cases xa : x∈A
  · refine ⟨S.erase b \ A,sdiff_subset,bn,fun h => (mem_sdiff.mp h).2 xa,?_⟩
    intro u hu v hv out e
    by_contra n
    have va : v∈A := by
      by_contra na
      exact out (mem_sdiff.mpr ⟨mem_erase.mpr ⟨n,hv⟩,na⟩)
    exact sep v va u hu (sym e)
  · refine ⟨A,sub,an,xa,?_⟩
    intro u hu v hv out e
    by_contra n
    exact sep u hu v (mem_sdiff.mpr ⟨mem_erase.mpr ⟨n,hv⟩,out⟩) e

private theorem side_neighbor {E : Edge} (sym : Undirected E) {S W : Vertices}
    (conn : Connected E S) {b : ℕ} (hb : b∈S) (sub : W⊆S.erase b)
    (wn : W.Nonempty) (side : Side E S b W) : ∃ u∈W, E b u := by
  have bo : b∉W := fun h => notMem_erase _ _ (sub h)
  obtain ⟨u,hu,v,hv,e⟩ := conn W (sub.trans (erase_subset ..)) wn
    ⟨b,mem_sdiff.mpr ⟨hb,bo⟩⟩
  have eq := side u hu v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2 e
  exact ⟨u,hu,eq ▸ sym e⟩

noncomputable def neighbors (E : Edge) (S : Vertices) (x : ℕ) : Vertices := by
  classical
  exact S.filter (E x)

@[simp] theorem mem_neighbors {E : Edge} {S : Vertices} {x y : ℕ} :
    y∈neighbors E S x ↔ y∈S ∧ E x y := by classical exact mem_filter

/-- In a bipartite graph this is precisely an induced subdivided claw:
choose three neighbors of x, each with a private second neighbor. Same-level
edges are excluded by the bipartition. -/
def LongClaw (E : Edge) (S : Vertices) : Prop :=
  ∃ x∈S, ∃ N⊆neighbors E S x, 3≤N.card ∧
    ∀ y∈N, ∃ u∈S, u≠x ∧ E y u ∧ ∀ z∈N, z≠y → ¬E z u

theorem claw_mono {E : Edge} {S U : Vertices} (sub : S⊆U) (h : LongClaw E S) :
    LongClaw E U := by
  obtain ⟨x,xs,N,ns,sz,arms⟩ := h
  refine ⟨x,sub xs,N,fun z hz => mem_neighbors.mpr
    ⟨sub (mem_neighbors.mp (ns hz)).1,(mem_neighbors.mp (ns hz)).2⟩,sz,?_⟩
  intro y hy
  obtain ⟨u,hu,n,e,p⟩ := arms y hy
  exact ⟨u,sub hu,n,e,p⟩

private theorem claw_of_cut_neighbors {E : Edge} (sym : Undirected E)
    (irr : ∀ x, ¬E x x) {S : Vertices} (conn : Connected E S) (x : ℕ)
    (xs : x∈S) (big : 3≤(neighbors E S x).card)
    (cuts : ∀ y∈neighbors E S x, ¬Legal E S y) : LongClaw E S := by
  refine ⟨x,xs,neighbors E S x,Subset.rfl,big,?_⟩
  intro y hy
  obtain ⟨ys,xy⟩ := mem_neighbors.mp hy
  obtain ⟨W,sub,wn,xo,side⟩ := cut_side (x:=x) sym ys (cuts y hy)
  obtain ⟨u,uw,yu⟩ := side_neighbor sym conn ys sub wn side
  refine ⟨u,mem_of_mem_erase (sub uw),fun eq => xo (eq ▸ uw),yu,?_⟩
  intro z hz ne zu
  obtain ⟨zs,xz⟩ := mem_neighbors.mp hz
  have out : z∉W := fun h => (fun eq : x=y => irr _ (eq ▸ xy)) (side z h x xs xo (sym xz))
  exact ne (side u uw z zs out (sym zu))

private theorem three_neighbors {E : Edge} {S : Vertices} {b x y z : ℕ}
    (xs : x∈S) (ys : y∈S) (zs : z∈S) (bx : E b x) (by' : E b y) (bz : E b z)
    (xy : x≠y) (xz : x≠z) (yz : y≠z) : 3≤(neighbors E S b).card := by
  classical
  have sub : {x,y,z}⊆neighbors E S b := by
    intro t ht
    simp only [mem_insert,mem_singleton] at ht
    rcases ht with rfl|rfl|rfl
    · exact mem_neighbors.mpr ⟨xs,bx⟩
    · exact mem_neighbors.mpr ⟨ys,by'⟩
    · exact mem_neighbors.mpr ⟨zs,bz⟩
  simpa [xy,xz,yz] using card_le_card sub

/-- If b lies on a cycle through x and another neighbor c, then b is
removable or has at least three neighbors. A connected set D avoiding x
and containing b,c supplies the alternate route around the cycle. -/
private theorem bypass {E : Edge} (sym : Undirected E) (irr : ∀ x, ¬E x x)
    {S D : Vertices} (conn : Connected E S) (cd : Connected E D)
    {x b c : ℕ} (xs : x∈S) (subD : D⊆S.erase x) (bd : b∈D) (cc : c∈D)
    (xb : E x b) (xc : E x c) (cb : c≠b) (cut : ¬Legal E S b) :
    3≤(neighbors E S b).card := by
  have bs := mem_of_mem_erase (subD bd)
  have cs := mem_of_mem_erase (subD cc)
  have nx : x≠b := fun eq => irr _ (eq ▸ xb)
  obtain ⟨W,sub,wn,xo,side⟩ := cut_side (x:=x) sym bs cut
  obtain ⟨t,tw,bt⟩ := side_neighbor sym conn bs sub wn side
  have co : c∉W := fun h => nx (side c h x xs xo (sym xc))
  let A := D ∩ insert b W
  have bA : b∈A := mem_inter.mpr ⟨bd,mem_insert_self ..⟩
  have cA : c∉A := fun h => ((mem_insert.mp (mem_inter.mp h).2).elim cb co)
  obtain ⟨p,pa,z,za,edge⟩ := cd A inter_subset_left ⟨b,bA⟩ ⟨c,mem_sdiff.mpr ⟨cc,cA⟩⟩
  obtain ⟨zd,out⟩ := mem_sdiff.mp za
  have zs := mem_of_mem_erase (subD zd)
  have zw : z∉W := fun h => out (mem_inter.mpr ⟨zd,mem_insert_of_mem h⟩)
  have zb : z≠b := fun eq => out (eq ▸ bA)
  have pb := (mem_insert.mp (mem_inter.mp pa).2).resolve_right
    (fun h => zb (side p h z zs zw edge))
  subst p
  exact three_neighbors xs (mem_of_mem_erase (sub tw)) zs (sym xb) bt edge
    (fun eq => xo (eq ▸ tw)) (mem_erase.mp (subD zd)).1.symm (fun eq => zw (eq ▸ tw))

theorem exists_legal {E : Edge} (sym : Undirected E) {S : Vertices} (conn : Connected E S)
    (size : 1<S.card) : ∃ x, Legal E S x := by
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<S.card)
  obtain ⟨y,hy,ne⟩ := exists_mem_ne size x
  obtain ⟨v,_,l⟩ := peel_outside sym conn (singleton_connected E x)
    ⟨x,mem_singleton_self x⟩ (singleton_subset_iff.mpr hx)
    ⟨y,mem_sdiff.mpr ⟨hy,by simpa using ne⟩⟩
  exact ⟨v,l⟩

private theorem low_legal {E : Edge} (sym : Undirected E) {S : Vertices} (conn : Connected E S)
    {v : ℕ} (vs : v∈S) (low : (neighbors E S v).card ≤ 1) : Legal E S v := by
  classical
  refine ⟨vs,?_⟩
  by_contra fail
  unfold Connected at fail
  push Not at fail
  obtain ⟨A,sub,an,bn,sep⟩ := fail
  let B := S.erase v \ A
  have subB : B⊆S.erase v := sdiff_subset
  have sideA : Side E S v A := by
    intro x hx y hy out e
    by_contra ne
    exact sep x hx y (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,hy⟩,out⟩) e
  have sideB : Side E S v B := by
    intro x hx y hy out e
    by_contra ne
    have ya : y∈A := by
      by_contra no
      exact out (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,hy⟩,no⟩)
    exact sep y ya x hx (sym e)
  obtain ⟨a,ha,ea⟩ := side_neighbor sym conn vs sub an sideA
  obtain ⟨b,hb,eb⟩ := side_neighbor sym conn vs subB bn sideB
  have eq := card_le_one.mp low a (mem_neighbors.mpr ⟨mem_of_mem_erase (sub ha),ea⟩)
    b (mem_neighbors.mpr ⟨mem_of_mem_erase (subB hb),eb⟩)
  exact (mem_sdiff.mp hb).2 (eq ▸ ha)

private theorem two_other {A : Vertices} (big : 3≤A.card) (l : ℕ) :
    ∃ b∈A, b≠l ∧ ∃ c∈A, c≠l ∧ c≠b := by
  obtain ⟨b,hb,bl⟩ := exists_mem_ne (by omega : 1<A.card) l
  have size : 1<(A.erase l).card := by
    by_cases h : l∈A
    · rw [card_erase_of_mem h]; omega
    · simpa [erase_eq_of_notMem h] using (by omega : 1<A.card)
  obtain ⟨c,hc,cb⟩ := exists_mem_ne size b
  exact ⟨b,hb,bl,c,mem_of_mem_erase hc,(mem_erase.mp hc).1,cb⟩

/-- If every opening exposes a target of the given color, high degree
forces three private arms; this includes graphs with cyclic blocks. -/
private theorem stuck_degree {E : Edge} (sym : Undirected E) {col : ℕ → Bool}
    (bip : ∀ ⦃u v⦄, E u v → col u≠col v) {S : Vertices} (conn : Connected E S)
    (free : ¬LongClaw E S) (k : Bool)
    (stuck : ∀ x, Legal E S x → ∃ t, Exposes E S x t ∧ col t=k) :
    ∀ x∈S, (neighbors E S x).card≤2 := by
  classical
  have irr (x : ℕ) : ¬E x x := fun e => bip e rfl
  have off {x} (lx : Legal E S x) : col x≠k := by
    obtain ⟨t,et,ct⟩ := stuck x lx
    exact ct ▸ bip (exposes_edge sym conn lx.1 et)
  have blue {x} (xs : x∈S) (cx : col x≠k) : (neighbors E S x).card≤2 := by
    by_contra! big
    apply free (claw_of_cut_neighbors sym irr conn x xs big ?_)
    intro y hy ly
    have cr := bip (mem_neighbors.mp hy).2
    have cy := off ly
    cases k <;> cases col x <;> cases col y <;> simp_all
  intro x xs
  by_contra! big
  by_cases cuts : ∀ y∈neighbors E S x, ¬Legal E S y
  · exact free (claw_of_cut_neighbors sym irr conn x xs big cuts)
  push Not at cuts
  obtain ⟨l,hl,ll⟩ := cuts
  obtain ⟨t,et,ct⟩ := stuck l ll
  obtain ⟨ls,xl⟩ := mem_neighbors.mp hl
  have xt := exposes_only sym et xs (sym xl) (fun h => irr _ (h ▸ xl)) ls
  subst t
  obtain ⟨b,hb,bl,c,hc,cl,cb⟩ := two_other big l
  obtain ⟨bs,xb⟩ := mem_neighbors.mp hb
  obtain ⟨cs,xc⟩ := mem_neighbors.mp hc
  let D := (S.erase l).erase x
  have cd : Connected E D := et.1.2
  have bd : b∈D := mem_erase.mpr ⟨fun h => irr _ (h ▸ xb),mem_erase.mpr ⟨bl,bs⟩⟩
  have cc : c∈D := mem_erase.mpr ⟨fun h => irr _ (h ▸ xc),mem_erase.mpr ⟨cl,cs⟩⟩
  have sub : D⊆S.erase x := fun _ hz => mem_erase.mpr ⟨(mem_erase.mp hz).1,
    mem_of_mem_erase (mem_of_mem_erase hz)⟩
  have cut : ¬Legal E S b := by
    intro lb
    obtain ⟨u,eu,_⟩ := stuck b lb
    obtain ⟨z,zd,zb,bz⟩ := neighbor cd bd cc cb
    have xu := exposes_only sym eu xs (sym xb) (fun h => irr _ (h ▸ xb)) bs
    have zu := exposes_only sym eu (mem_of_mem_erase (sub zd)) bz zb bs
    exact (mem_erase.mp (sub zd)).1 (zu.trans xu.symm)
  have bound := blue bs (ct ▸ bip (sym xb))
  have high := bypass sym irr conn cd xs sub bd cc xb xc cb cut
  omega

private noncomputable def crossEdges (E : Edge) (R B : Vertices) := by
  classical
  exact (R ×ˢ B).filter (fun p => E p.1 p.2)

private theorem cross_count (E : Edge) (R B : Vertices) :
    (crossEdges E R B).card=∑ x∈R, (neighbors E B x).card := by
  classical
  simp only [crossEdges,neighbors,Finset.card_filter,Finset.sum_product]

private theorem cross_swap {E : Edge} (sym : Undirected E) (R B : Vertices) :
    (crossEdges E R B).card=(crossEdges E B R).card := by
  classical
  simp only [crossEdges,Finset.card_filter,Finset.sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro r _
  rw [show E r b ↔ E b r from ⟨fun h => sym h, fun h => sym h⟩]

private noncomputable def coloredEdges (E : Edge) (col : ℕ → Bool) (k : Bool)
    (S : Vertices) := crossEdges E (S.filter (fun z => col z=k)) (S.filter (fun z => col z≠k))

private theorem colored_mem (E : Edge) (col : ℕ → Bool) (k : Bool) (S : Vertices) (p : ℕ×ℕ) :
    p∈coloredEdges E col k S ↔
    ((p.1∈S ∧ col p.1=k) ∧ (p.2∈S ∧ col p.2≠k)) ∧ E p.1 p.2 := by
  classical simp only [coloredEdges,crossEdges,mem_filter,mem_product]

private theorem spanning_bound {E : Edge} (sym : Undirected E) {col : ℕ → Bool}
    (bip : ∀ ⦃u v⦄, E u v → col u≠col v) (k : Bool) (S : Vertices) (conn : Connected E S) :
    S.card≤(coloredEdges E col k S).card+1 := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases small : S.card≤1
    · omega
    obtain ⟨v,hv⟩ := exists_legal sym conn (by omega)
    obtain ⟨z,hz,zv⟩ := exists_mem_ne (by omega : 1<S.card) v
    obtain ⟨y,ys,yv,vy⟩ := neighbor conn hv.1 hz zv
    have prev := ih _ (erase_ssubset hv.1) hv.2
    have sub : coloredEdges E col k (S.erase v)⊆coloredEdges E col k S := by
      intro p h
      obtain ⟨⟨⟨a,ca⟩,b,cb⟩,e⟩ := (colored_mem ..).mp h
      exact (colored_mem ..).mpr ⟨⟨⟨mem_of_mem_erase a,ca⟩,mem_of_mem_erase b,cb⟩,e⟩
    have strict : coloredEdges E col k (S.erase v)⊂coloredEdges E col k S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨sub,?_⟩
      intro eq
      have different := bip vy
      by_cases red : col v=k
      · have h := (colored_mem E col k S (v,y)).mpr
          ⟨⟨⟨hv.1,red⟩,ys,red ▸ different.symm⟩,vy⟩
        rw [←eq,colored_mem] at h
        exact notMem_erase _ _ h.1.1.1
      · have cy : col y=k := by
          revert different red
          generalize col v=a; generalize col y=b
          cases a <;> cases b <;> cases k <;> decide
        have h := (colored_mem E col k S (y,v)).mpr ⟨⟨⟨ys,cy⟩,hv.1,red⟩,sym vy⟩
        rw [←eq,colored_mem] at h
        exact notMem_erase _ _ h.1.2.1
    have := card_lt_card strict
    rw [card_erase_of_mem hv.1] at prev
    omega

/-- At even order a silent collection of targets on a single side can
remain protected after an opening. -/
theorem safe_opening {E : Edge} (sym : Undirected E) {col : ℕ → Bool}
    (bip : ∀ ⦃u v⦄, E u v → col u≠col v) {S : Vertices} (conn : Connected E S)
    (free : ¬LongClaw E S) (k : Bool) (size : 1<S.card) (even : Even S.card) :
    ∃ x, Legal E S x ∧ ∀ t, Exposes E S x t → col t≠k := by
  classical
  by_contra! stuck
  have H (x) (lx : Legal E S x) : ∃ t, Exposes E S x t ∧ col t=k := stuck x lx
  have cap := stuck_degree sym bip conn free k H
  let R := S.filter (fun z => col z=k)
  let B := S.filter (fun z => col z≠k)
  have total : R.card+B.card=S.card := card_filter_add_card_filter_not ..
  have cr (x) (hx : x∈R) : neighbors E B x=neighbors E S x := by
    ext y; simp only [mem_neighbors,B,mem_filter]
    have cx := (mem_filter.mp hx).2
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,cx ▸ (bip h.2).symm⟩,h.2⟩⟩
  have full : (crossEdges E R B).card=2*R.card := by
    rw [cross_count]
    have eq (x) (hx : x∈R) : (neighbors E B x).card=2 := by
      obtain ⟨xs,cx⟩ := mem_filter.mp hx
      rw [cr x hx]
      have max := cap x xs
      by_contra nottwo
      have lx := low_legal sym conn xs (by omega)
      obtain ⟨t,et,ct⟩ := H x lx
      exact bip (exposes_edge sym conn xs et) (cx.trans ct.symm)
    simp only [sum_congr rfl eq,sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm]
  obtain ⟨l,ll⟩ := exists_legal sym conn size
  obtain ⟨t,et,ct⟩ := H l ll
  have lc := bip (exposes_edge sym conn ll.1 et)
  have lb : l∈B := mem_filter.mpr ⟨ll.1,ct ▸ lc⟩
  have short : (neighbors E R l).card<2 := by
    apply Nat.lt_succ_of_le
    apply card_le_one.mpr
    intro u hu v hv
    have one {z} (hz : z∈neighbors E R l) : z=t := by
      obtain ⟨zr,lz⟩ := mem_neighbors.mp hz
      exact exposes_only sym et (mem_filter.mp zr).1 lz
        (fun e => bip (e ▸ lz) rfl) ll.1
    exact (one hu).trans (one hv).symm
  have bound (x) (hx : x∈B) : (neighbors E R x).card≤2 := by
    apply le_trans (card_le_card ?_) (cap x (mem_filter.mp hx).1)
    intro z hz
    obtain ⟨zr,xz⟩ := mem_neighbors.mp hz
    exact mem_neighbors.mpr ⟨(mem_filter.mp zr).1,xz⟩
  have small := Finset.sum_lt_sum bound ⟨l,lb,short⟩
  rw [←cross_count,cross_swap sym B R,full] at small
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at small
  have span := spanning_bound sym bip k S conn
  change S.card≤(crossEdges E R B).card+1 at span
  rw [full] at span
  obtain ⟨m,hm⟩ := even
  omega

/-- The center and the three length-two arms of the canonical seven-vertex tree. -/
inductive ClawVertex
  | center
  | middle (i : Fin 3)
  | tip (i : Fin 3)
  deriving DecidableEq

def ClawVertex.adj : ClawVertex → ClawVertex → Prop
  | .center, .middle _ | .middle _, .center => True
  | .middle i, .tip j | .tip j, .middle i => i=j
  | _, _ => False

def InducedClaw (E : Edge) (S : Vertices) : Prop :=
  ∃ f : ClawVertex → ℕ, (∀ v, f v∈S) ∧ Function.Injective f ∧
    ∀ v w, E (f v) (f w) ↔ ClawVertex.adj v w

/-- The private-neighbor certificate has exactly the induced edges of S₂,₂,₂. -/
theorem longClaw_iff_induced {E : Edge} (sym : Undirected E) {col : ℕ → Bool}
    (bip : ∀ ⦃u v⦄, E u v → col u≠col v) (S : Vertices) :
    LongClaw E S ↔ InducedClaw E S := by
  classical
  constructor
  · rintro ⟨x,xs,N,sub,big,arms⟩
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<N.card)
    obtain ⟨b,hb,ba,c,hc,ca,cb⟩ := two_other big a
    let M : Fin 3 → ℕ := fun i => if i=0 then a else if i=1 then b else c
    have three (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by omega
    have mn (i : Fin 3) : M i∈N := by rcases three i with rfl|rfl|rfl <;> simp_all [M]
    have mi : Function.Injective M := by
      intro i j h
      rcases three i with rfl|rfl|rfl <;> rcases three j with rfl|rfl|rfl <;> simp_all [M]
    have xm (i : Fin 3) := (mem_neighbors.mp (sub (mn i))).2
    choose U us ux mu priv using fun i => arms (M i) (mn i)
    have off (i) : col x≠col (M i) := bip (xm i)
    have onC (i) : col (U i)=col x := by
      have e := bip (mu i)
      have f := off i
      revert e f
      generalize col (M i)=a; generalize col (U i)=b; generalize col x=c
      cases a <;> cases b <;> cases c <;> decide
    have cross (i j) : E (M i) (U j) ↔ i=j := by
      constructor
      · intro edge
        by_contra ne
        exact priv j (M i) (mn i) (fun h => ne (mi h)) edge
      · rintro rfl; exact mu _
    have ui : Function.Injective U := by
      intro i j h
      exact (cross i j).mp (h ▸ mu i)
    let F : ClawVertex → ℕ
      | .center => x
      | .middle i => M i
      | .tip i => U i
    refine ⟨F,?_,?_,?_⟩
    · intro v
      cases v with
      | center => exact xs
      | middle i => exact (mem_neighbors.mp (sub (mn i))).1
      | tip i => exact us i
    · have diff (i j) : M i≠U j := fun h => (off i).symm ((congrArg col h).trans (onC j))
      have xc (i) : x≠M i := fun h => off i (congrArg col h)
      intro v w h
      cases v <;> cases w
      · rfl
      · exact ((xc _) h).elim
      · exact ((ux _) h.symm).elim
      · exact ((xc _) h.symm).elim
      · exact congrArg ClawVertex.middle (mi h)
      · exact ((diff _ _) h).elim
      · exact ((ux _) h).elim
      · exact ((diff _ _) h.symm).elim
      · exact congrArg ClawVertex.tip (ui h)
    · intro v w
      have no {p q} (h : col p=col q) : ¬E p q := fun e => bip e h
      have mm (i j) : col (M i)=col (M j) := by
        have a := off i
        have b := off j
        revert a b
        generalize col x=a; generalize col (M i)=b; generalize col (M j)=c
        cases a <;> cases b <;> cases c <;> decide
      have mx (i) := sym (xm i)
      have back (i j) : E (U j) (M i) ↔ i=j := ⟨fun e => (cross i j).mp (sym e),
        fun h => sym ((cross i j).mpr h)⟩
      cases v <;> cases w <;> simp [F,ClawVertex.adj,xm,mx,cross,back,no rfl,
        fun i => no (onC i),fun i => no (onC i).symm,fun i j => no (mm i j),
        fun i j => no ((onC i).trans (onC j).symm)]
  · rintro ⟨F,fs,inj,adj⟩
    let M := fun i => F (.middle i)
    have mi : Function.Injective M := fun _ _ h => ClawVertex.middle.inj (inj h)
    let N := Finset.univ.image M
    have ns : N⊆neighbors E S (F .center) := by
      intro z hz
      obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      exact mem_neighbors.mpr ⟨fs _,(adj .center (.middle i)).mpr trivial⟩
    refine ⟨F .center,fs _,N,ns,?_,?_⟩
    · simp [N,card_image_of_injective _ mi]
    · intro y hy
      obtain ⟨i,_,rfl⟩ := mem_image.mp hy
      refine ⟨F (.tip i),fs _,(fun h => by have hc := inj h; cases hc),(adj (.middle i) (.tip i)).mpr rfl,?_⟩
      intro z hz ne e
      obtain ⟨j,_,rfl⟩ := mem_image.mp hz
      exact ne (congrArg M ((adj (.middle j) (.tip i)).mp e))

end GraphGrabbing
#print axioms GraphGrabbing.safe_opening
#print axioms GraphGrabbing.longClaw_iff_induced
