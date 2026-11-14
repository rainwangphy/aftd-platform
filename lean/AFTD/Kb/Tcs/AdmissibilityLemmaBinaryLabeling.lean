import AFTD.Prelude
import AFTD.Kb.Tcs.IsTotalEdgeIrregularLabeling
import AFTD.Kb.Tcs.SimpleGraphEndpointSumEdges
import AFTD.Kb.Tcs.AdmissibilityLemmaNecessity
import AFTD.Kb.Tcs.AdmissibilityLemmaSufficiency

/-!
# admissibility_lemma_binary_labeling

Topic: graphs   Node: 8f775fcec681

Provenance: formalization of a published result. Source: arXiv:2611.16338, Lemma 2.1

Let s ≥ 3, let G be a finite simple graph, and let φ : V → ℕ be a vertex labeling such that φ(v) ∈ {1, s} for all v. Let a = |E_2|, b = |E_{s+1}|, and c = |E_{2s}| be the counts of edges with endpoint label sums 2, s + 1, and 2s, where E_r is the set of edges whose endpoint labels sum to r. Then φ extends to a total edge irregular s-labeling of G if and only if a ≤ s, b ≤ s, c ≤ s, a + b ≤ 2s - 1, b + c ≤ 2s - 1, and a + b + c ≤ 3s - 2.
-/

open scoped Classical in
/-- Admissibility lemma for binary vertex labelings (Lemma 2.1). -/
theorem admissibility_lemma_binary_labeling {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : ℕ) (hs : 3 ≤ s) (φ : V → ℕ)
    (hφ : ∀ v : V, φ v = 1 ∨ φ v = s) :
    let a := (simple_graph_endpoint_sum_edges G φ 2).card
    let b := (simple_graph_endpoint_sum_edges G φ (s + 1)).card
    let c := (simple_graph_endpoint_sum_edges G φ (2 * s)).card
    (∃ ψ : G.edgeSet → ℕ, is_total_edge_irregular_labeling G s φ ψ) ↔
      (a ≤ s ∧ b ≤ s ∧ c ≤ s ∧ a + b ≤ 2 * s - 1 ∧ b + c ≤ 2 * s - 1 ∧ a + b + c ≤ 3 * s - 2) := by
  intro a b c
  exact ⟨admissibility_lemma_necessity G s hs φ hφ, admissibility_lemma_sufficiency G s hs φ hφ⟩
