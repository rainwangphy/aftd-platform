import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSemisaturationIsolatedEdgeBound
import AFTD.Kb.Tcs.DigraphHasIsolatedEdge
import AFTD.Kb.Tcs.DigraphIsOriented
import AFTD.Kb.Tcs.DigraphEdgeCount
import AFTD.Kb.Tcs.DigraphSsat

/-!
# digraph_semisaturation_bounded_of_isolated_edge

Topic: graphs   Node: e4d23e6f216e

Provenance: formalization of a published result. Source: arXiv:2610.18600 Lemma 2.1

Let G : Digraph V be a finite oriented digraph on vertex type V with DecidableEq V and DecidableRel G.Adj such that digraph_is_oriented G and digraph_has_isolated_edge G hold. Then the semisaturation function is bounded: there exist C : ℕ and n₀ : ℕ such that for all n ≥ n₀, digraph_ssat n G ≤ C.
-/

/-- Bounded semisaturation for oriented graphs containing an isolated edge (Lemma 2.1). -/
theorem digraph_semisaturation_bounded_of_isolated_edge {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (hG : digraph_is_oriented G) (he : digraph_has_isolated_edge G) : ∃ C : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, digraph_ssat n G ≤ C := by
  obtain ⟨n₀, hn₀⟩ := digraph_semisaturation_isolated_edge_bound G hG he
  exact ⟨3 * (digraph_edge_count G - 1), n₀, hn₀⟩
