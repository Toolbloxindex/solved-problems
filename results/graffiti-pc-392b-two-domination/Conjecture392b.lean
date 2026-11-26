import Color392
import Cover392
namespace Graffiti392.Graph
open Finset Classical
noncomputable section
variable {n : Nat} (G : Graph n)

/-- Graffiti.pc 392b, announced in January 2010. -/
theorem conjecture392b (hn : 2 < n) (hc : G.Connected) :
    G.gammaTwo ≤ G.matching (univ \ G.minimum) + G.minimum.card + G.exceptional.card := by
  classical
  obtain ⟨c,good⟩ := G.adequate_cut hn hc
  let U := univ \ G.paid
  obtain ⟨s,matching,cover⟩ := G.crossing_cover U c
  have rem {x : V n} (h : x ∉ G.paid) : x ∈ U := mem_sdiff.mpr ⟨mem_univ _,h⟩
  have dom : G.TwoDominates (s ∪ G.paid) := by
    intro x hx
    have xs : x ∉ s := fun h => hx (mem_union_left _ h)
    have xp : x ∉ G.paid := fun h => hx (mem_union_right _ h)
    apply (good x xp).trans (card_le_card ?_)
    intro y hy
    obtain ⟨ha,choice⟩ := mem_filter.mp hy
    refine mem_inter.mpr ⟨ha,?_⟩
    by_cases yp : y ∈ G.paid
    · exact mem_union_right _ yp
    have edge : G.cross U c x y :=
      ⟨rem xp,rem yp,G.mem_nbr.mp ha,choice.resolve_left yp⟩
    exact mem_union_left _ ((cover x y edge).resolve_left xs)
  have bigger : U ⊆ univ \ G.minimum := by
    intro x hx
    exact mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_sdiff.mp hx).2 (G.mem_paid.mpr (.inl h))⟩
  obtain ⟨ss,f,inj,hf⟩ := matching
  have m := G.le_matching (show G.Matches (univ \ G.minimum) s from
    ⟨ss.trans bigger,f,inj,fun i => ⟨bigger (hf i).1,(hf i).2⟩⟩)
  have d := G.gammaTwo_le dom
  have bound := card_union_le s G.paid
  have p : G.paid.card ≤ G.minimum.card + G.exceptional.card := card_union_le ..
  omega

end
end Graffiti392.Graph
