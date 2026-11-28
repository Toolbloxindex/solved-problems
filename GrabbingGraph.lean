module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Push

@[expose] public section

namespace GraphGrabbing
open Finset
abbrev Vertices := Finset ℕ
abbrev Edge := ℕ → ℕ → Prop
abbrev Undirected (E : Edge) := ∀ ⦃x y⦄, E x y → E y x

/-- Every nontrivial partition of the remaining vertices has a crossing edge.
This includes the empty terminal position. -/
def Connected (E : Edge) (S : Vertices) : Prop :=
  ∀ A ⊆ S, A.Nonempty → (S \ A).Nonempty →
    ∃ u ∈ A, ∃ v ∈ S \ A, E u v

def Legal (E : Edge) (S : Vertices) (v : ℕ) := v ∈ S ∧ Connected E (S.erase v)

def Exposes (E : Edge) (S : Vertices) (v t : ℕ) :=
  Legal E (S.erase v) t ∧ ¬ Legal E S t

private theorem sub_erase {S A : Vertices} {x : ℕ} (sub : A ⊆ S) (miss : x ∉ A) :
    A ⊆ S.erase x := by
  intro y hy
  exact mem_erase.mpr ⟨fun h => miss (h ▸ hy), sub hy⟩

theorem neighbor {E : Edge} {S : Vertices} (h : Connected E S) {x y : ℕ}
    (hx : x∈S) (hy : y∈S) (ne : y≠x) : ∃ z∈S, z≠x ∧ E x z := by
  obtain ⟨u,hu,z,hz,e⟩ := h {x} (singleton_subset_iff.mpr hx) ⟨x,by simp⟩
    ⟨y,mem_sdiff.mpr ⟨hy,by simpa using ne⟩⟩
  have hu := mem_singleton.mp hu
  subst u
  obtain ⟨hz, hn⟩ := mem_sdiff.mp hz
  exact ⟨z,hz,by simpa using hn,e⟩

theorem insert_connected {E : Edge} (sym : Undirected E) {S : Vertices} (h : Connected E S)
    {x y : ℕ} (hy : y∈S) (e : E x y) : Connected E (insert x S) := by
  intro A sub ha hb
  by_cases left : (A ∩ S).Nonempty
  · by_cases right : (S \ (A ∩ S)).Nonempty
    · obtain ⟨u,hu,v,hv,uv⟩ := h _ inter_subset_right left right
      obtain ⟨vs,out⟩ := mem_sdiff.mp hv
      exact ⟨u,(mem_inter.mp hu).1,v,mem_sdiff.mpr ⟨mem_insert_of_mem vs,
        fun a => out (mem_inter.mpr ⟨a,vs⟩)⟩,uv⟩
    · obtain ⟨z,hz⟩ := hb
      obtain ⟨zs,za⟩ := mem_sdiff.mp hz
      have all (t) (ht : t∈S) : t∈A := by
        by_contra hn
        exact right ⟨t,mem_sdiff.mpr ⟨ht,fun q => hn (mem_inter.mp q).1⟩⟩
      have zx := (mem_insert.mp zs).resolve_right (fun hs => za (all _ hs))
      subst z
      exact ⟨y,all _ hy,x,hz,sym e⟩
  · obtain ⟨z,hz⟩ := ha
    have none (t) (ht : t∈A) : t∉S := fun s => left ⟨t,mem_inter.mpr ⟨ht,s⟩⟩
    have zx := (mem_insert.mp (sub hz)).resolve_right (none _ hz)
    subst z
    exact ⟨x,hz,y,mem_sdiff.mpr ⟨mem_insert_of_mem hy,fun a => none _ a hy⟩,e⟩

/-- Only a leaf can expose a previously illegal vertex. Every surviving
neighbor of the opening is that newly exposed vertex. -/
theorem exposes_only {E : Edge} (sym : Undirected E) {S : Vertices} {x t z : ℕ}
    (un : Exposes E S x t) (hz : z∈S) (edge : E x z) (nz : z≠x)
    (hx : x∈S) : z=t := by
  obtain ⟨⟨ht,conn⟩,bad⟩ := un
  obtain ⟨ne,ts⟩ := mem_erase.mp ht
  by_contra nt
  have joined := insert_connected sym conn (mem_erase.mpr ⟨nt,mem_erase.mpr ⟨nz,hz⟩⟩) edge
  rw [show (S.erase x).erase t=(S.erase t).erase x by ext; simp [and_left_comm],insert_erase (mem_erase.mpr ⟨ne.symm,hx⟩)] at joined
  exact bad ⟨ts,joined⟩

theorem exposes_edge {E : Edge} (sym : Undirected E) {S : Vertices} (h : Connected E S)
    {x t : ℕ} (hx : x∈S) (un : Exposes E S x t) : E x t := by
  obtain ⟨ne,ts⟩ := mem_erase.mp un.1.1
  obtain ⟨z,hz,nz,e⟩ := neighbor h hx ts ne
  rwa [exposes_only sym un hz e nz hx] at e

theorem exposes_unique {E : Edge} (sym : Undirected E) (loop : ∀ x, ¬E x x)
    {S : Vertices} (h : Connected E S) {x t u : ℕ} (hx : x∈S)
    (a : Exposes E S x t) (b : Exposes E S x u) : t=u := by
  have e := exposes_edge sym h hx a
  exact exposes_only sym b (mem_of_mem_erase a.1.1) e (fun q => loop x (q ▸ e)) hx

/-- A connected set can be grown from any nonempty connected subset.
In particular there is a removable vertex outside a prescribed root. -/
theorem peel_outside {E : Edge} (sym : Undirected E) {S A : Vertices}
    (cs : Connected E S) (ca : Connected E A) (ha : A.Nonempty) (sub : A⊆S)
    (extra : (S \ A).Nonempty) : ∃ x∈S \ A, Legal E S x := by
  classical
  generalize eq : (S \ A).card = n
  induction n using Nat.strong_induction_on generalizing A with
  | ind n ih =>
    obtain ⟨u,hu,x,hx,e⟩ := cs A sub ha extra
    obtain ⟨xs,xa⟩ := mem_sdiff.mp hx
    let B := insert x A
    have cb : Connected E B := insert_connected sym ca hu (sym e)
    have bs : B⊆S := insert_subset xs sub
    by_cases more : (S \ B).Nonempty
    · have ss : S \ B ⊂ S \ A := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
        · intro z hz
          obtain ⟨zs,zn⟩ := mem_sdiff.mp hz
          exact mem_sdiff.mpr ⟨zs,fun a => zn (mem_insert_of_mem a)⟩
        intro equal
        have : x∈S \ B := equal ▸ hx
        simp [B] at this
      obtain ⟨z,hz,legal⟩ := ih (S \ B).card (eq ▸ card_lt_card ss) cb
        ⟨x,mem_insert_self ..⟩ bs more rfl
      exact ⟨z,(Finset.ssubset_iff_subset_ne.mp ss).1 hz,legal⟩
    · have eqB : B=S := by
        apply Subset.antisymm bs
        intro z hz
        by_contra zz
        exact more ⟨z,mem_sdiff.mpr ⟨hz,zz⟩⟩
      refine ⟨x,hx,xs,?_⟩
      rw [←eqB]
      simpa [B,xa] using ca

theorem singleton_connected (E : Edge) (x : ℕ) : Connected E {x} := by
  intro A sub ha hb
  obtain ⟨v,hv⟩ := ha
  obtain ⟨z,hz⟩ := hb
  obtain ⟨zs,za⟩ := mem_sdiff.mp hz
  have eq := mem_singleton.mp (sub hv)
  exact (za ((mem_singleton.mp zs).symm ▸ eq ▸ hv)).elim

end GraphGrabbing
