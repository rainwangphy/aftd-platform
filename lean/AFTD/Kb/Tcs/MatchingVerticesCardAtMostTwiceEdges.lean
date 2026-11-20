import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# matching_vertices_card_at_most_twice_edges

Topic: graphs   Node: 6c2cc9bafb0d

Provenance: helper lemma. The matching-cardinality proof used in the proved complement-matching theorem.

The vertices of a matching with k edges fit in a set of at most 2k vertices.
-/

theorem matching_vertices_card_at_most_twice_edges {V : Type*} [Fintype V] {k : ℕ}
    {H : SimpleGraph V} (M : H.Subgraph) (hM : M.IsMatching) (hMk : M.edgeSet.ncard = k) :
    ∃ S : Finset V, (∀ x, x ∈ M.verts → x ∈ S) ∧ S.card ≤ 2*k := by
  classical
  refine ⟨M.verts.toFinset, by simp, ?_⟩
  have h := in1076_matching_twice_card hM
  rw [hMk] at h
  have hc : M.verts.toFinset.card = M.verts.ncard := by
    rw [Set.ncard_eq_toFinset_card M.verts, Set.toFinite_toFinset]
  omega
