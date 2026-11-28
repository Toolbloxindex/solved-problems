module

public import MixedPaths

@[expose] public section

namespace KaylesRays.MixedPaths
open LiteralKayles Sum

variable {V : Type} [DecidableEq V]

def putShort (n : Nat) : PairedGraph.Vertex (Site V) → Site V
  | .host v => v
  | .left i | .right i => inr (n,⟨i.val,by omega⟩)


def paddedEdge (E : V → V → Bool) (u : V) (p : Nat) : Site V → Site V → Bool
  | inr (m,i), inr (n,j) => decide (m≠p) && decide (n≠p) && siteEdge E u (inr (m,i)) (inr (n,j))
  | a, b => siteEdge E u a b

private theorem padded_pres (E : V → V → Bool) (u : V) (s : Finset V)
    (ids : Finset Nat) (f : Arms) (p : Nat) (hp : f p=pathPrefix 1)
    (v : Site V) (hv : v∈mixed s ids f) (w : Site V) (hw : w∈mixed s ids f) :
    paddedEdge E u p v w = siteEdge E u v w := by
  rcases v with (v|⟨m,i⟩) <;> rcases w with (w|⟨n,j⟩)
  · rfl
  · rfl
  · rfl
  · by_cases e : m=n
    · subst n
      by_cases h : m=p
      · subst m
        have hi : i=0 := by
          apply Fin.ext
          have b := (mem_ray .. |>.mp hv).2
          rw [hp,mem_pathPrefix] at b
          omega
        have hj : j=0 := by
          apply Fin.ext
          have b := (mem_ray .. |>.mp hw).2
          rw [hp,mem_pathPrefix] at b
          omega
        subst i j
        simp [paddedEdge,siteEdge,FiveMoves.rayEdge]
      · simp [paddedEdge,siteEdge,h]
    · simp [paddedEdge,siteEdge,e]

private theorem padded_leaf (E : V → V → Bool) (u : V) (p : Nat) :
    PairedGraph.LeafAt (paddedEdge E u p) (inl u) (inr (p,0)) := by
  refine ⟨by simp,?_⟩
  rintro (v|⟨n,i⟩) <;> simp [paddedEdge,siteEdge]

/-- With a live pendant leaf, an additional attached two-vertex path
is equal in value to a disjoint singleton. -/
theorem two_shift (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (f : Arms) {n : Nat} (hn : n∉ids)
    {p : Nat} (hp : p∈ids) (leaf : f p=pathPrefix 1) :
    score E u s (insert n ids) (replace f n (pathPrefix 2)) = score E u s ids f ^^^ 1 := by
  let B := mixed s ids f
  let P := paddedEdge E u p
  let D := PairedGraph.adj P (inl u)
  let T := PairedGraph.board B PairedGraph.two ∅
  change value (siteEdge E u) (mixed s (insert n ids) (replace f n (pathPrefix 2))) =
    value (siteEdge E u) B ^^^ 1
  have base : value P B = value (siteEdge E u) B := by
    simpa only [Finset.image_id] using
      value_image (siteEdge E u) P id B (fun _ _ _ _ e => e) (padded_pres E u s ids f p leaf)
  have pair := PairedGraph.pendant_p2_shift P (padded_leaf E u p) B
    (show inl u∈B by simp [B,hu]) (show inr (p,0)∈B by simp [B,hp,leaf])
  have eq : T.image (putShort n) = mixed s (insert n ids) (replace f n (pathPrefix 2)) := by
    rw [arm_insert s ids f hn]
    ext v
    simp only [Finset.mem_image,Finset.mem_union]
    constructor
    · rintro ⟨w,hw,rfl⟩
      cases w with
      | host w => exact Or.inl (PairedGraph.host_mem .. |>.mp hw)
      | left i =>
        have h := (PairedGraph.left_mem .. |>.mp hw)
        exact Or.inr (Finset.mem_image.mpr ⟨_,by
          have hi : i=0 ∨ i=1 := by simpa [PairedGraph.two] using h
          rcases hi with rfl|rfl <;> decide,rfl⟩)
      | right i => simp [T] at hw
    · rintro (h|h)
      · exact ⟨.host v,PairedGraph.host_mem .. |>.mpr h,rfl⟩
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
        have ik : i.val<2 := (mem_pathPrefix i 2).mp hi
        let j : Fin 4 := ⟨i.val,by omega⟩
        have jj : j=0 ∨ j=1 := by
          have e : i.val=0 ∨ i.val=1 := by omega
          exact e.imp Fin.ext Fin.ext
        exact ⟨.left j,PairedGraph.left_mem .. |>.mpr (by simpa [PairedGraph.two] using jj),rfl⟩
  have inHost {v : Site V} (h : PairedGraph.Vertex.host v∈T) : v∈B :=
    PairedGraph.host_mem .. |>.mp h
  have noRay (i : Fin 5) : inr (n,i) ∉ B := by simp [B,hn]
  have inj : Set.InjOn (putShort n) (↑T : Set (PairedGraph.Vertex (Site V))) := by
    intro v hv w hw e
    change v∈T at hv
    change w∈T at hw
    cases v <;> cases w
    all_goals try solve | simp [T] at hv | simp [T] at hw
    · simpa [putShort] using e
    · cases e
      exact (noRay _ (inHost hv)).elim
    · cases e
      exact (noRay _ (inHost hw)).elim
    · simp only [putShort,Sum.inr.injEq,Prod.mk.injEq,Fin.mk.injEq,PairedGraph.Vertex.left.injEq] at e ⊢
      exact Fin.ext e.2
  have lift_zero (i : Fin 4) : (⟨i.val,by omega⟩ : Fin 5)=0 ↔ i=0 := by
    constructor
    · intro b
      exact Fin.ext (congrArg (fun j : Fin 5 => j.val) b)
    · intro b
      exact Fin.ext (congrArg (fun j : Fin 4 => j.val) b)
  have pres : ∀ v∈T, ∀ w∈T, siteEdge E u (putShort n v) (putShort n w) = D v w := by
    intro v hv w hw
    cases v <;> cases w
    all_goals try solve | simp [T] at hv | simp [T] at hw
    · exact (padded_pres E u s ids f p leaf _ (inHost hv) _ (inHost hw)).symm
    · rename_i v i
      rcases v with (v|⟨m,j⟩)
      · simp [putShort,siteEdge,D,PairedGraph.adj,lift_zero]
      · have mne : m≠n := fun h => hn (h ▸ (mem_ray .. |>.mp (inHost hv)).1)
        simp [putShort,siteEdge,D,PairedGraph.adj,mne]
    · rename_i i w
      rcases w with (w|⟨m,j⟩)
      · simp [putShort,siteEdge,D,PairedGraph.adj,lift_zero]
      · have mne : n≠m := fun h => hn (h.symm ▸ (mem_ray .. |>.mp (inHost hw)).1)
        simp [putShort,siteEdge,D,PairedGraph.adj,mne]
    · simp [putShort,siteEdge,D,PairedGraph.adj,PairedGraph.path,FiveMoves.rayEdge]
  rw [← eq,value_image D _ _ _ inj pres,pair,base]


def arms (kind : Nat → Nat) : Arms := fun n => pathPrefix (kind n)

def liveKinds (ids : Finset Nat) (kind : Nat → Nat) :=
  ∀ n∈ids, kind n=5 ∨ kind n=3 ∨ kind n=1

def count (ids : Finset Nat) (kind : Nat → Nat) (size : Nat) :=
  (ids.filter fun n => kind n=size).card

theorem count_pos (ids : Finset Nat) (kind : Nat → Nat) (size : Nat) :
    0<count ids kind size ↔ ∃ n∈ids, kind n=size := by
  simp [count,Finset.card_pos,Finset.Nonempty]

theorem count_insert (ids : Finset Nat) (kind : Nat → Nat) {n : Nat} (hn : n∉ids) (size : Nat) :
    count (insert n ids) kind size = count ids kind size + if kind n=size then 1 else 0 := by
  by_cases h : kind n=size
  · have hm : n ∉ ids.filter (fun n => kind n=size) := by simp [hn]
    simp [count,Finset.filter_insert,h,Finset.card_insert_of_notMem hm]
  · simp [count,Finset.filter_insert,h]

theorem count_erase (ids : Finset Nat) (kind : Nat → Nat) {n : Nat} (hn : n∈ids) (size : Nat) :
    count (ids.erase n) kind size = count ids kind size - if kind n=size then 1 else 0 := by
  have e := count_insert (ids.erase n) kind (Finset.notMem_erase n ids) size
  rw [Finset.insert_erase hn] at e
  omega

def alter (kind : Nat → Nat) (n length : Nat) : Nat → Nat := fun m => if m=n then length else kind m

theorem arms_alter (kind : Nat → Nat) (n length : Nat) :
    arms (alter kind n length) = replace (arms kind) n (pathPrefix length) := by
  funext m
  by_cases e : m=n <;> simp [arms,alter,replace,e]

theorem count_alter (ids : Finset Nat) (kind : Nat → Nat) {n : Nat} (hn : n∈ids)
    (length size : Nat) :
    count ids (alter kind n length) size =
      (count ids kind size - if kind n=size then 1 else 0) +
        if length=size then 1 else 0 := by
  have h : count (ids.erase n) (alter kind n length) size = count (ids.erase n) kind size := by
    unfold count
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i hi
    simp [alter,(Finset.mem_erase.mp hi).1]
  have e := count_insert (ids.erase n) (alter kind n length) (Finset.notMem_erase n ids) size
  rw [Finset.insert_erase hn,h,count_erase ids kind hn] at e
  have here : alter kind n length n = length := by simp [alter]
  rwa [here] at e

theorem arms_replace_back (f : Arms) {n : Nat} (a : Finset (Fin 5))
    (ha : f n=a) : replace f n a = f := by
  funext m
  by_cases e : m=n <;> simp [replace,e,ha]

def odd (n : Nat) : Bool := decide (n%2=1)

def contribution (v n : Nat) := if odd n then v else 0

private theorem contribution_add (v n : Nat) :
    contribution v (n+1) = contribution v n ^^^ v := by
  by_cases h : n%2=1
  · have hn : ¬(n+1)%2=1 := by omega
    simp [contribution,odd,h,hn]
  · have hn : (n+1)%2=1 := by omega
    simp [contribution,odd,h,hn]

local instance : Std.Commutative Nat.xor := ⟨Nat.xor_comm⟩
local instance : Std.Associative Nat.xor := ⟨Nat.xor_assoc⟩

theorem inventory_xor (ids : Finset Nat) (kind w : Nat → Nat) (ok : liveKinds ids kind) :
    ids.fold Nat.xor 0 (fun n => w (kind n)) =
      contribution (w 5) (count ids kind 5) ^^^
      contribution (w 3) (count ids kind 3) ^^^
      contribution (w 1) (count ids kind 1) := by
  induction ids using Finset.induction_on with
  | empty => simp [count,contribution,odd]
  | @insert n ids hn ih =>
    have rest : liveKinds ids kind := fun m hm => ok m (Finset.mem_insert_of_mem hm)
    rw [Finset.fold_insert hn,ih rest,count_insert ids kind hn,count_insert ids kind hn,
      count_insert ids kind hn]
    rcases ok n (Finset.mem_insert_self n ids) with e|e|e <;>
      simp [e,contribution_add] <;> ac_rfl

private theorem length_values :
    (value path (pathPrefix 5),value path (pathPrefix 3),value path (pathPrefix 1)) = (3,2,1) ∧
    (value path ((pathPrefix 5).erase 0),value path ((pathPrefix 3).erase 0),
      value path ((pathPrefix 1).erase 0)) = (0,1,0) ∧
    (value path (drop path (pathPrefix 5) 0),value path (drop path (pathPrefix 3) 0),
      value path (drop path (pathPrefix 1) 0)) = (2,1,0) := by decide +kernel

def detachedXor (ids : Finset Nat) (kind : Nat → Nat) : Nat :=
  contribution 3 (count ids kind 5) ^^^ contribution 2 (count ids kind 3) ^^^
    (odd (count ids kind 1)).toNat

theorem detached_full (E : V → V → Bool) (u : V) (s : Finset V) (ids : Finset Nat)
    (kind : Nat → Nat) (ok : liveKinds ids kind) (hu : u∉s) :
    score E u s ids (arms kind) = value E s ^^^ detachedXor ids kind := by
  have e := inventory_xor ids kind (fun l => value path (pathPrefix l)) ok
  have a := congrArg Prod.fst length_values.1
  have b := congrArg (fun p => p.2.1) length_values.1
  have c := congrArg (fun p => p.2.2) length_values.1
  simp only at a b c
  rw [detached E u s ids _ hu]
  change value E s ^^^ ids.fold Nat.xor 0 (fun n => value path (pathPrefix (kind n))) = _
  rw [e,a,b,c]
  unfold detachedXor
  cases h : odd (count ids kind 1) <;> simp [contribution,h]

theorem detached_trim (E : V → V → Bool) (u : V) (s : Finset V) (ids : Finset Nat)
    (kind : Nat → Nat) (ok : liveKinds ids kind) (hu : u∉s) :
    score E u s ids (fun n => ((arms kind) n).erase 0) = value E s ^^^ (count ids kind 3 % 2) := by
  have e := inventory_xor ids kind (fun l => value path ((pathPrefix l).erase 0)) ok
  have a := congrArg Prod.fst length_values.2.1
  have b := congrArg (fun p => p.2.1) length_values.2.1
  have c := congrArg (fun p => p.2.2) length_values.2.1
  simp only at a b c
  rw [detached E u s ids _ hu]
  change value E s ^^^ ids.fold Nat.xor 0 (fun n => value path ((pathPrefix (kind n)).erase 0)) = _
  rw [e,a,b,c]
  have zero (n : Nat) : contribution 0 n = 0 := by unfold contribution; split <;> rfl
  simp only [zero,Nat.zero_xor,Nat.xor_zero]
  congr 1
  by_cases h : count ids kind 3%2=1
  · simp [contribution,odd,h]
  · have e : count ids kind 3%2=0 := by omega
    simp [contribution,odd,e]

theorem arm_root_after (E : V → V → Bool) (u : V) (s : Finset V) (ids : Finset Nat)
    (kind : Nat → Nat) (ok : liveKinds ids kind) {n : Nat} (hn : n∈ids) :
    after E u s ids (arms kind) (inr (n,0)) =
      (value E (s.erase u) ^^^ detachedXor ids kind) ^^^ (if kind n=3 then 3 else 1) := by
  have empty : u∉s.erase u := Finset.notMem_erase u s
  have em : n∉ids.erase n := Finset.notMem_erase n ids
  have ins : insert n (ids.erase n) = ids := Finset.insert_erase hn
  have initial := detached_insert E u (s.erase u) (ids.erase n) (arms kind) em
    ((arms kind) n) (Or.inl empty)
  rw [ins,arms_replace_back (arms kind) _ rfl,detached_full E u _ _ _ ok empty] at initial
  have played := detached_insert E u (s.erase u) (ids.erase n) (arms kind) em
    (drop path ((arms kind) n) 0) (Or.inl empty)
  rw [ins] at played
  have a := congrArg Prod.fst length_values.1
  have b := congrArg (fun p => p.2.1) length_values.1
  have c := congrArg (fun p => p.2.2) length_values.1
  have da := congrArg Prod.fst length_values.2.2
  have db := congrArg (fun p => p.2.1) length_values.2.2
  have dc := congrArg (fun p => p.2.2) length_values.2.2
  simp only at a b c da db dc
  unfold after
  rw [arm_drop,ite_eq_left rfl]
  change score E u (s.erase u) ids (replace (arms kind) n (drop path ((arms kind) n) 0)) = _
  rw [played,initial,Nat.xor_assoc]
  congr 1
  rcases ok n hn with h|h|h <;> simp only [arms,h,a,b,c,da,db,dc] <;> decide

end KaylesRays.MixedPaths

namespace KaylesRays.MixedPaths
open LiteralKayles Sum

variable {V : Type} [DecidableEq V]

/-- The three sizes can share a labeling. Only their counts and the parity
of the positive leaf count occur in the interior move set. -/
def RayOptions (f : Nat → Nat → Bool → Nat) (x c : Nat) (z : Bool) (e k : Nat) : Prop :=
  e ^^^ 1 = k ∨
  (0<c ∧ e ^^^ 3 = k) ∨
  (0<x ∧ (f (x-1) c false ^^^ 1 = k ∨ f (x-1) c true ^^^ 1 = k ∨ f (x-1) (c+1) z = k)) ∨
  (0<c ∧ (f x (c-1) false = k ∨ f x (c-1) true = k))

private theorem odd_step (n : Nat) : odd (n+1) = !odd n := by
  unfold odd
  by_cases h : n%2=1
  · have e : (n+1)%2=0 := by omega
    simp [h,e]
  · have e : (n+1)%2=1 := by omega
    simp [h,e]

set_option maxHeartbeats 1200000 in
theorem ray_options (E : V → V → Bool) (u : V) (s : Finset V) (hu : u∈s)
    (ids : Finset Nat) (kind : Nat → Nat) (ok : liveKinds ids kind)
    (f : Nat → Nat → Bool → Nat)
    (leaves : 0<count ids kind 1)
    (lower : ∀ js types, liveKinds js types → 0<count js types 1 →
      2*count js types 5+count js types 3 < 2*count ids kind 5+count ids kind 3 →
      score E u s js (arms types) = f (count js types 5) (count js types 3) (odd (count js types 1))) :
    ∀ k, (∃ n∈ids, ∃ i∈(arms kind) n, after E u s ids (arms kind) (inr (n,i)) = k) ↔
      RayOptions f (count ids kind 5) (count ids kind 3) (odd (count ids kind 1))
        (value E (s.erase u) ^^^ detachedXor ids kind) k := by
  let x := count ids kind 5
  let c := count ids kind 3
  let l := count ids kind 1
  let e := value E (s.erase u) ^^^ detachedXor ids kind
  let play := fun n i => after E u s ids (arms kind) (inr (n,i))
  obtain ⟨p,hp,hp1⟩ := (count_pos ids kind 1).mp leaves
  have root (n : Nat) (hn : n∈ids) : play n 0 = e ^^^ (if kind n=3 then 3 else 1) :=
    arm_root_after E u s ids kind ok hn
  have base (n : Nat) (hn : n∈ids) (nn : kind n=5 ∨ kind n=3) :
      0<count (ids.erase n) kind 1 := by
    rw [count_erase ids kind hn]
    rcases nn with nn|nn <;> simpa [nn] using leaves
  have erasedKinds (n : Nat) : liveKinds (ids.erase n) kind :=
    fun m hm => ok m (Finset.mem_of_mem_erase hm)
  have alteredKinds (n size : Nat) (hs : size=3 ∨ size=1) : liveKinds ids (alter kind n size) := by
    intro m hm
    by_cases eq : m=n
    · simp only [alter,eq,ite_true]
      exact Or.inr hs
    · simpa only [alter,ite_eq_right eq] using ok m hm
  have five_moves (n : Nat) (hn : n∈ids) (h5 : kind n=5) :
      play n 1 = f (x-1) c (odd l) ^^^ 1 ∧
      play n 2 = f (x-1) c (!odd l) ^^^ 1 ∧
      play n 3 = f (x-1) c (odd l) ^^^ 1 ∧
      play n 4 = f (x-1) (c+1) (odd l) := by
    have ins : insert n (ids.erase n) = ids := Finset.insert_erase hn
    have fresh : n∉ids.erase n := Finset.notMem_erase n ids
    have moved := five E u s hu (ids.erase n) (arms kind) fresh
    dsimp only at moved
    rw [ins, arms_replace_back (arms kind) _ (by simp [arms,h5])] at moved
    obtain ⟨a,b,d,t⟩ := moved
    have pos : 0<count ids kind 5 := (count_pos ids kind 5).mpr ⟨n,hn,h5⟩
    have eraseScore := lower (ids.erase n) kind (erasedKinds n) (base n hn (Or.inl h5))
      (by
        simp [count_erase ids kind hn,h5]
        omega)
    simp [count_erase ids kind hn,h5] at eraseScore
    rw [eraseScore] at a
    have leafLive : 0<count ids (alter kind n 1) 1 := by
      simp [count_alter ids kind hn,h5]
    have threeLive : 0<count ids (alter kind n 3) 1 := by
      simpa [count_alter ids kind hn,h5] using leaves
    have one := lower ids (alter kind n 1) (alteredKinds n 1 (Or.inr rfl)) leafLive (by
      simp [count_alter ids kind hn,h5]
      omega)
    have three := lower ids (alter kind n 3) (alteredKinds n 3 (Or.inl rfl)) threeLive (by
      simp [count_alter ids kind hn,h5]
      change 2*(x-1)+(c+1) < 2*x+c
      omega)
    rw [arms_alter] at one three
    have np : p≠n := by
      intro eq
      rw [eq,h5] at hp1
      contradiction
    have shift := two_shift E u s hu (ids.erase n) (arms kind) fresh
      (Finset.mem_erase.mpr ⟨np,hp⟩) (by simp [arms,hp1])
    rw [ins] at shift
    rw [one] at b
    rw [shift,eraseScore] at d
    rw [three] at t
    exact ⟨a,by simpa [x,c,l,count_alter ids kind hn,h5,odd_step] using b,
      d,by simpa [x,c,l,count_alter ids kind hn,h5] using t⟩
  have three_moves (n : Nat) (hn : n∈ids) (h3 : kind n=3) :
      play n 1 = f x (c-1) (odd l) ∧ play n 2 = f x (c-1) (!odd l) := by
    have ins : insert n (ids.erase n) = ids := Finset.insert_erase hn
    have fresh : n∉ids.erase n := Finset.notMem_erase n ids
    have moved := MixedPaths.three E u s hu (ids.erase n) (arms kind) fresh
    dsimp only at moved
    rw [ins,arms_replace_back (arms kind) _ (by simp [arms,h3])] at moved
    have pos : 0<count ids kind 3 := (count_pos ids kind 3).mpr ⟨n,hn,h3⟩
    have a := lower (ids.erase n) kind (erasedKinds n) (base n hn (Or.inr h3)) (by
      simp [count_erase ids kind hn,h3]
      omega)
    have leafLive : 0<count ids (alter kind n 1) 1 := by
      simp [count_alter ids kind hn,h3]
    have b := lower ids (alter kind n 1) (alteredKinds n 1 (Or.inr rfl)) leafLive (by
      simp [count_alter ids kind hn,h3]
      omega)
    rw [arms_alter] at b
    rw [a] at moved
    exact ⟨by simpa [x,c,l,count_erase ids kind hn,h3] using moved.1,
      by simpa [x,c,l,b,count_alter ids kind hn,h3,odd_step] using moved.2⟩
  have rootP (n : Nat) (hn : n∈ids) : 0 ∈ (arms kind) n := by
    rcases ok n hn with a|a|a <;> simp [arms,a]
  have local_menu (n : Nat) (hn : n∈ids) (k : Nat) :
      (∃ i∈(arms kind) n, play n i=k) ↔
        (kind n=1 ∧ e ^^^ 1=k) ∨
        (kind n=5 ∧ (e ^^^ 1=k ∨
          f (x-1) c false ^^^ 1=k ∨ f (x-1) c true ^^^ 1=k ∨ f (x-1) (c+1) (odd l)=k)) ∨
        (kind n=3 ∧ (e ^^^ 3=k ∨ f x (c-1) false=k ∨ f x (c-1) true=k)) := by
    rcases ok n hn with h5|h3|h1
    · obtain ⟨a,b,d,t⟩ := five_moves n hn h5
      have r : play n 0 = e ^^^ 1 := by simpa [h5] using root n hn
      have reach (i : Fin 5) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by
        have b := i.isLt
        have q : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 := by omega
        rcases q with q|q|q|q|q
        · exact Or.inl (Fin.ext q)
        · exact Or.inr (Or.inl (Fin.ext q))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext q)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext q))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext q))))
      simp [h5]
      cases h : odd l <;> simp only [h,Bool.not_false,Bool.not_true] at a b d t ⊢
      all_goals
        constructor
        · rintro ⟨i,_,hi⟩
          rcases reach i with rfl|rfl|rfl|rfl|rfl <;> simp only [r,a,b,d,t] at hi <;> tauto
        · simp only [arms,h5,mem_pathPrefix]
          intro H
          rcases H with H|H|H|H
          all_goals first
            | exact ⟨0,by decide,r.trans H⟩
            | exact ⟨1,by decide,a.trans H⟩
            | exact ⟨2,by decide,b.trans H⟩
            | exact ⟨4,by decide,t.trans H⟩
    · obtain ⟨a,b⟩ := three_moves n hn h3
      have r : play n 0 = e ^^^ 3 := by simpa [h3] using root n hn
      simp [h3]
      cases h : odd l <;> simp only [h,Bool.not_false,Bool.not_true] at a b ⊢
      all_goals
        constructor
        · rintro ⟨i,hi,he⟩
          have bound : i.val<3 := by simpa [arms,h3] using hi
          have q : i.val=0 ∨ i.val=1 ∨ i.val=2 := by omega
          have eq : i=0 ∨ i=1 ∨ i=2 := by
            rcases q with q|q|q
            · exact Or.inl (Fin.ext q)
            · exact Or.inr (Or.inl (Fin.ext q))
            · exact Or.inr (Or.inr (Fin.ext q))
          rcases eq with rfl|rfl|rfl <;> simp only [r,a,b] at he <;> tauto
        · simp only [arms,h3,mem_pathPrefix]
          intro H
          rcases H with H|H|H
          all_goals first
            | exact ⟨0,by decide,r.trans H⟩
            | exact ⟨1,by decide,a.trans H⟩
            | exact ⟨2,by decide,b.trans H⟩
    · have rr : play n 0 = e ^^^ 1 := by simpa [h1] using root n hn
      simp [h1]
      constructor
      · rintro ⟨i,hi,e⟩
        have v : i.val<1 := by simpa [arms,h1] using hi
        have eq : i=0 := Fin.ext (by omega)
        subst i
        exact rr.symm.trans e
      · intro h
        exact ⟨0,rootP n hn,rr.trans h⟩
  intro k
  change (∃ n∈ids, ∃ i∈(arms kind) n, play n i=k) ↔ RayOptions f x c (odd l) e k
  have xpos : 0<x ↔ ∃ n∈ids, kind n=5 := count_pos ids kind 5
  have cpos : 0<c ↔ ∃ n∈ids, kind n=3 := count_pos ids kind 3
  unfold RayOptions
  rw [xpos,cpos]
  constructor
  · rintro ⟨n,hn,h⟩
    rcases (local_menu n hn k).mp h with ⟨_,h⟩|⟨five,h|h⟩|⟨three,h|h⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨⟨n,hn,five⟩,h⟩))
    · exact Or.inr (Or.inl ⟨⟨n,hn,three⟩,h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨⟨n,hn,three⟩,h⟩))
  · rintro (h|⟨⟨n,hn,three⟩,h⟩|⟨⟨n,hn,five⟩,h⟩|⟨⟨n,hn,three⟩,h⟩)
    · exact ⟨p,hp,(local_menu p hp k).mpr (Or.inl ⟨hp1,h⟩)⟩
    · exact ⟨n,hn,(local_menu n hn k).mpr (Or.inr (Or.inr ⟨three,Or.inl h⟩))⟩
    · exact ⟨n,hn,(local_menu n hn k).mpr (Or.inr (Or.inl ⟨five,Or.inr h⟩))⟩
    · exact ⟨n,hn,(local_menu n hn k).mpr (Or.inr (Or.inr ⟨three,Or.inr h⟩))⟩

end KaylesRays.MixedPaths
