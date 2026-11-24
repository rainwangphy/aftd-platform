import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.FourByFiveDefectIncidenceImpossible
import AFTD.Kb.Tcs.BoundaryFiveBlocksEssentialEdgeCrossDefectPattern
import AFTD.Kb.Tcs.IsKExtendable

/-!
# boundary_five_blocks_minimal_no_full_cross

Topic: graphs   Node: d657e61bc42b

Provenance: helper lemma. OP-1957: no full cross vertex in the nonclique two-five-block degree route.

In the stated four-block partition with two five-vertex selected blocks, minimum degree at least 2k+2, the 2k separator property and minimal k-extendibility, every vertex of the first selected block has a nonneighbor in the opposite selected block.
-/

theorem boundary_five_blocks_minimal_no_full_cross
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (hmin : is_minimally_k_extendable G k) :
    ∀ x ∈ A, 1 ≤ (C.filter (fun c => ¬ G.Adj x c)).card := by
  classical
  intro x hx
  by_contra hn
  have hz : (C.filter (fun c => ¬ G.Adj x c)).card = 0 := by omega
  have hfull : ∀ c ∈ C, G.Adj x c := by
    intro c hc
    by_contra h
    have hp : 0 < (C.filter (fun c => ¬ G.Adj x c)).card :=
      Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hc,h⟩⟩
    omega
  apply four_by_five_defect_incidence_impossible (A.erase x) C (fun a c => ¬ G.Adj a c)
  · simp [Finset.card_erase_of_mem hx, hA]
  · exact hC
  · intro a ha
    have haA : a ∈ A := (Finset.mem_erase.mp ha).2
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hAB haA h
    have hbudget := anticomplete_neighbor_defect_bound G B a haB (hnoAB a haA)
      (2*k+4) 2 (by simp; omega) (by have := hdegree a; omega)
    apply le_trans (Finset.card_le_card ?_) hbudget
    intro c hc
    simp only [Finset.mem_filter] at hc
    have hcB : c ∉ B := fun h => Finset.disjoint_left.mp hBC h hc.1
    have hca : c ≠ a := fun h => Finset.disjoint_left.mp hAC haA (h ▸ hc.1)
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hca, hcB⟩, hc.2⟩
  · intro c hc
    have hxc := hfull c hc
    have he : ¬ is_k_extendable (G.deleteEdges {s(x,c)}) k :=
      hmin.2 s(x,c) (by simpa using hxc)
    have hp := boundary_five_blocks_essential_edge_cross_defect_pattern k hk G A B C D
      hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree hsep
      hmin.1 x c hx hc hxc he
    have hc2 := hp.2 (by omega)
    have heq : (A.erase x).filter (fun a => ¬ G.Adj a c) = A.filter (fun a => ¬ G.Adj a c) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_,ha⟩,hn⟩; exact ⟨ha,hn⟩
      · rintro ⟨ha,hn⟩
        refine ⟨⟨?_,ha⟩,hn⟩
        intro h
        subst a
        exact hn hxc
    rw [heq]
    omega
