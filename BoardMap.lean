module

public import GameValue

@[expose] public section

namespace LiteralKayles

/-- An isomorphism onto an image needs to preserve only the live vertices. -/
theorem value_image {V W : Type} [DecidableEq V] [DecidableEq W]
    (E : V → V → Bool) (D : W → W → Bool) (f : V → W) (s : Finset V)
    (inj : Set.InjOn f (s : Set V))
    (pres : ∀ v∈s, ∀ w∈s, D (f v) (f w) = E v w) :
    value D (s.image f) = value E s := by
  let src := Function.Embedding.subtype (· ∈ s)
  let dst : {v // v ∈ s} ↪ W :=
    ⟨fun v => f v.val,fun v w h => Subtype.ext (inj v.property w.property h)⟩
  let subEdge (v w : {v // v ∈ s}) := E v.val w.val
  have image_eq : s.attach.map dst = s.image f := by
    ext k
    simp only [Finset.mem_map,Finset.mem_attach,true_and,Finset.mem_image]
    constructor
    · rintro ⟨⟨v,hv⟩,rfl⟩
      exact ⟨v,hv,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨⟨v,hv⟩,rfl⟩
  have src_eq : s.attach.map src = s := Finset.attach_map_val
  calc
    value D (s.image f) = value D (s.attach.map dst) := congrArg (value D) image_eq.symm
    _ = value subEdge s.attach := value_map subEdge D dst (fun v w => pres v.val v.property w.val w.property) _
    _ = value E (s.attach.map src) := (value_map subEdge E src (fun _ _ => rfl) _).symm
    _ = value E s := congrArg (value E) src_eq

end LiteralKayles
