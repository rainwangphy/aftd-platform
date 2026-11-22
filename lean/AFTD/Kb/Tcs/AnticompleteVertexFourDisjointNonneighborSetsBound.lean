import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.FourDisjointSubsetsCardSumLe

/-!
# anticomplete_vertex_four_disjoint_nonneighbor_sets_bound

Topic: graphs   Node: 2cb6fa8a3df3

Provenance: helper lemma. OP-1957: graph-to-count transfer for the size-five block forced-edge route (IN-1126).

If a vertex is anticomplete to a block and its degree is within r of the number of vertices outside the block other than itself, then four pairwise disjoint sets of its non-neighbors (other than itself) have at most r vertices outside the block in total.
-/

theorem anticomplete_vertex_four_disjoint_nonneighbor_sets_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Q : Finset V) (v : V) (hv : v ∉ Q)
    (hanti : ∀ b ∈ Q, ¬ G.Adj v b) (d r : ℕ)
    (hsize : Fintype.card V = Q.card + d + 1)
    (hdeg : d ≤ (G.neighborFinset v).card + r)
    (s1 s2 s3 s4 : Finset V)
    (hs : ∀ w, (w ∈ s1 ∨ w ∈ s2 ∨ w ∈ s3 ∨ w ∈ s4) → w ≠ v ∧ ¬ G.Adj v w)
    (d12 : Disjoint s1 s2) (d13 : Disjoint s1 s3) (d14 : Disjoint s1 s4)
    (d23 : Disjoint s2 s3) (d24 : Disjoint s2 s4) (d34 : Disjoint s3 s4) :
    (s1 \ Q).card + (s2 \ Q).card + (s3 \ Q).card + (s4 \ Q).card ≤ r := by
  have hb := anticomplete_neighbor_defect_bound G Q v hv hanti d r hsize hdeg
  have hsub : ∀ s : Finset V, (∀ w ∈ s, w ≠ v ∧ ¬ G.Adj v w) →
      s \ Q ⊆ ((Finset.univ \ Q).erase v) \ G.neighborFinset v := by
    intro s hs' w hw
    rw [Finset.mem_sdiff] at hw
    obtain ⟨h1, h2⟩ := hs' w hw.1
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    exact ⟨⟨h1, hw.2⟩, h2⟩
  have := four_disjoint_subsets_card_sum_le (s1 \ Q) (s2 \ Q) (s3 \ Q) (s4 \ Q) _
    (hsub s1 (fun w hw => hs w (Or.inl hw)))
    (hsub s2 (fun w hw => hs w (Or.inr (Or.inl hw))))
    (hsub s3 (fun w hw => hs w (Or.inr (Or.inr (Or.inl hw)))))
    (hsub s4 (fun w hw => hs w (Or.inr (Or.inr (Or.inr hw)))))
    (Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset d12))
    (Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset d13))
    (Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset d14))
    (Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset d23))
    (Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset d24))
    (Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset d34))
  omega
