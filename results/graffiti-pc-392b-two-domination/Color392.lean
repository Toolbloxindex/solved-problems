import Cut392
namespace Graffiti392.Graph
open Finset Classical
noncomputable section
variable {n : Nat} (G : Graph n)

/-- Every nonempty subset of the unpaid chain interiors has a vertex with
at most one neighbor in the subset. Connectedness rules out a cycle component. -/
private theorem peel (hc : G.Connected) {S : Finset (V n)} (hs : S ⊆ G.inside)
    (hne : S.Nonempty) : ∃ v ∈ S, (G.nbr v ∩ S).card ≤ 1 := by
  obtain ⟨u,hu⟩ := G.minimum_nonempty (let ⟨x,_⟩ := hne; ⟨x⟩)
  have out : u ∉ S := fun h => (G.mem_inside.mp (hs h)).2.2 (G.mem_paid.mpr (.inl hu))
  obtain ⟨v,hv,w,hw,hadj⟩ := hc S hne ⟨u,out⟩
  have strict : (G.nbr v ∩ S).card < (G.nbr v).card := by
    apply card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left,fun eq => hw
      (mem_inter.mp (eq ▸ G.mem_nbr.mpr hadj)).2⟩
  have d := (G.mem_inside.mp (hs hv)).1
  change (G.nbr v).card = 2 at d
  exact ⟨v,hv,by omega⟩

private theorem color_subset (hc : G.Connected) (S : Finset (V n)) (hs : S ⊆ G.inside) :
    ∃ c : V n → Bool, ∀ x ∈ S, ∀ y ∈ S, G.adj x y → c x ≠ c y := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨v,hv,small⟩ := G.peel hc hs hne
    obtain ⟨c,valid⟩ := color_subset hc (S.erase v) ((erase_subset ..).trans hs)
    let b := if h : (G.nbr v ∩ S).Nonempty then !(c h.choose) else false
    let f (x : V n) := if x = v then b else c x
    have incident {y : V n} (hy : y ∈ S) (a : G.adj v y) : f v ≠ f y := by
      have ny : y ≠ v := fun e => G.loopless v (e ▸ a)
      have yy : y ∈ G.nbr v ∩ S := mem_inter.mpr ⟨G.mem_nbr.mpr a,hy⟩
      have h : (G.nbr v ∩ S).Nonempty := ⟨y,yy⟩
      have e := (card_le_one.mp small) _ h.choose_spec y yy
      simp [f,b,h,ny,e]
    refine ⟨f,?_⟩
    intro x hx y hy a
    by_cases ex : x = v
    · subst x; exact incident hy a
    by_cases ey : y = v
    · subst y; exact Ne.symm (incident hx (G.symm a))
    simpa [f,ex,ey] using valid x (mem_erase.mpr ⟨ex,hx⟩) y (mem_erase.mpr ⟨ey,hy⟩) a
  · exact ⟨fun _ => false,fun _ hx => (hne ⟨_,hx⟩).elim⟩
termination_by S.card
decreasing_by exact card_erase_lt_of_mem hv

def useful (c : V n → Bool) (x : V n) :=
  (G.nbr x).filter (fun y => y ∈ G.paid ∨ c x ≠ c y)

private theorem degree_pos (hn : 2 < n) (hc : G.Connected) (v : V n) : 0 < G.degree v := by
  have other : ∃ w : V n, w ∉ ({v} : Finset _) := by
    by_contra! bad
    have sub : (univ : Finset (V n)) ⊆ {v} := fun w _ => bad w
    have h := card_le_card sub
    simp at h
    omega
  obtain ⟨x,hx,y,_,a⟩ := hc {v} (singleton_nonempty _) other
  obtain rfl := mem_singleton.mp hx
  exact card_pos.mpr ⟨y,G.mem_nbr.mpr a⟩

theorem adequate_cut (hn : 2 < n) (hc : G.Connected) :
    ∃ c : V n → Bool, ∀ x ∉ G.paid, 2 ≤ (G.useful c x).card := by
  classical
  obtain ⟨b,hb⟩ := G.color_subset hc G.inside (fun _ h => h)
  let seed (x : V n) := if x ∈ G.inside then b x else decide (G.degree x = 2)
  obtain ⟨c,hcfix,free⟩ := G.extend_cut G.fixed seed
  refine ⟨c,?_⟩
  intro x hx
  have notOne {w : V n} (h : w ∉ G.paid) : (G.twoNbr w).card ≠ 1 :=
    fun e => h (G.mem_paid.mpr (.inr (G.mem_exceptional.mpr e)))
  have atMost (w : V n) : (G.twoNbr w).card ≤ G.degree w := card_le_card (G.twoNbr_sub w)
  have cHigh {v w : V n} (a : G.adj v w) (dv : G.degree v ≠ 2) (dw : G.degree w = 2) :
      c v = false := by
    have p : 0 < (G.twoNbr v).card := card_pos.mpr ⟨w,G.mem_twoNbr.mpr ⟨a,dw⟩⟩
    have f := hcfix v (.inr p)
    have o : v ∉ G.inside := fun h => dv (G.mem_inside.mp h).1
    simpa [seed,o,dv] using f
  have cIsolated {v : V n} (dv : G.degree v = 2) (z : (G.twoNbr v).card = 0) :
      c v = true := by
    have o : v ∉ G.inside := fun h => by have := (G.mem_inside.mp h).2.1; omega
    simpa only [seed,ite_eq_right o,decide_eq_true dv] using hcfix v (.inl dv)
  by_cases dx : G.degree x = 2
  · suffices sub : G.nbr x ⊆ G.useful c x by
      have h := card_le_card sub
      change (G.nbr x).card = 2 at dx
      omega
    intro y hy
    apply mem_filter.mpr
    refine ⟨hy,?_⟩
    by_cases paid : y ∈ G.paid
    · exact .inl paid
    apply Or.inr
    have a := G.mem_nbr.mp hy
    by_cases q : (G.twoNbr x).card = 0
    · have dy : G.degree y ≠ 2 := fun h => by
        have t := card_pos.mpr (show (G.twoNbr x).Nonempty from ⟨y,G.mem_twoNbr.mpr ⟨a,h⟩⟩)
        omega
      rw [cIsolated dx q,cHigh (G.symm a) dy dx]
      decide
    · have t := atMost x
      have o := notOne hx
      have tx : (G.twoNbr x).card = 2 := by omega
      have ix := G.mem_inside.mpr ⟨dx,tx,hx⟩
      have dy := (G.mem_twoNbr.mp ((G.all_neighbors_two dx tx).symm ▸ hy)).2
      have ypos := card_pos.mpr (show (G.twoNbr y).Nonempty from ⟨x,G.mem_twoNbr.mpr ⟨G.symm a,dx⟩⟩)
      have ty := atMost y
      have oy := notOne paid
      have iy := G.mem_inside.mpr ⟨dy,by omega,paid⟩
      have cx := hcfix x (.inl dx)
      have cy := hcfix y (.inl dy)
      rw [cx,cy]
      simpa only [seed,ite_eq_left ix,ite_eq_left iy] using hb x ix y iy a
  · by_cases q : 0 < (G.twoNbr x).card
    · have sub : G.twoNbr x ⊆ G.useful c x := by
        intro y hy
        obtain ⟨a,dy⟩ := G.mem_twoNbr.mp hy
        refine mem_filter.mpr ⟨G.mem_nbr.mpr a,?_⟩
        by_cases paid : y ∈ G.paid
        · exact .inl paid
        have noTwo : (G.twoNbr y).card ≠ 2 := fun h => dx
          (G.mem_twoNbr.mp ((G.all_neighbors_two dy h).symm ▸ G.mem_nbr.mpr (G.symm a))).2
        have oy := notOne paid
        have ty := atMost y
        have z : (G.twoNbr y).card = 0 := by omega
        exact .inr (by rw [cHigh a dx dy,cIsolated dy z]; decide)
      have t := card_le_card sub
      have o := notOne hx
      omega
    · have bal := free x (fun h => h.elim dx q)
      have tot := G.degree_split c x
      have dm : 2 < G.degree x := by
        have pd := G.degree_pos hn hc x
        by_contra! low
        exact hx (G.mem_paid.mpr (.inl (G.mem_minimum.mpr (fun y => by
          have := G.degree_pos hn hc y
          omega))))
      have sub : G.opp c x ⊆ G.useful c x := by
        intro y hy
        obtain ⟨ha,ho⟩ := mem_filter.mp hy
        exact mem_filter.mpr ⟨ha,.inr ho⟩
      have h := card_le_card sub
      omega

end
end Graffiti392.Graph
