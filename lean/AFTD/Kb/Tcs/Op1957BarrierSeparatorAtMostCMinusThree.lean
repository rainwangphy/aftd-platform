import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# op1957_barrier_separator_at_most_c_minus_three

Topic: graphs   Node: 3dd9341b7bc4

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Barrier separator at most c minus three.
-/

set_option maxHeartbeats 2000000

theorem op1957_barrier_separator_at_most_c_minus_three
    (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (S U D : Finset (Fin (4*k))) (y : Fin (4*k))
    (hD : D.card=2*k-c) (hyD : y ∉ D) (hyU : y ∉ U) (hUD : Disjoint U D)
    (hnoD : ∀ d ∈ D, ¬ G.Adj y d) (hnoU : ∀ u ∈ U, ¬ G.Adj y u)
    (hdegree : 2*k+2 ≤ (G.neighborFinset y).card)
    (hSU : S.card ≤ U.card) :
    S.card+3 ≤ c := by
  classical
  have hsize : Fintype.card (Fin (4*k)) = D.card+(2*k+c-1)+1 := by
    simp only [Fintype.card_fin]
    omega
  have hd : 2*k+c-1 ≤ (G.neighborFinset y).card+(c-3) := by omega
  have hb := anticomplete_neighbor_defect_bound G D y hyD hnoD (2*k+c-1) (c-3) hsize hd
  have hsub : U ⊆ (((Finset.univ \ D).erase y) \ G.neighborFinset y) := by
    intro u hu
    have hune : u ≠ y := fun h => hyU (h ▸ hu)
    have huD : u ∉ D := fun h => Finset.disjoint_left.mp hUD hu h
    simp only [Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,
      SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hune,huD⟩,hnoU u hu⟩
  have hU : U.card ≤ c-3 := (Finset.card_le_card hsub).trans hb
  omega
