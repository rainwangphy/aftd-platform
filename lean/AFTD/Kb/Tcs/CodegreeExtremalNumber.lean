import AFTD.Prelude
import AFTD.Kb.Tcs.IsThreeUniform
import AFTD.Kb.Tcs.IsHypergraphFree
import AFTD.Kb.Tcs.MinPairCodegree

/-!
# codegree_extremal_number

Topic: combinatorics   Node: 4dfd4dd1d4fc

Provenance: formalization of a published result. Source: arXiv:2611.12582 Section 1

For a natural number n and a hypergraph F on vertex type W, the real-valued codegree extremal number codegree_extremal_number n F is the supremum in ℝ over all hypergraphs H on Fin n satisfying is_three_uniform H and is_hypergraph_free H F of min_pair_codegree n H cast to ℝ.
-/

/-- The real-valued codegree extremal number ex₂(n, F) is the supremum in ℝ of δ₂(H) over all 3-uniform F-free hypergraphs H on Fin n. -/
noncomputable def codegree_extremal_number (n : ℕ) {W : Type*} (F : Finset (Finset W)) : ℝ := open Classical in
  ⨆ (H : Finset (Finset (Fin n))) (_h_unif : is_three_uniform H) (_h_free : is_hypergraph_free H F),
    (min_pair_codegree n H : ℝ)
