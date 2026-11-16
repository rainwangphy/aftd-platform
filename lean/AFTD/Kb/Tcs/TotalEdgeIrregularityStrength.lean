import AFTD.Prelude
import AFTD.Kb.Tcs.IsTotalEdgeIrregularLabeling

/-!
# total_edge_irregularity_strength

Topic: graphs   Node: 82252a7ea27c

Provenance: formalization of a published result. Source: arXiv:2611.16338 Section 1

The total edge irregularity strength of a simple graph G is the least positive integer s such that G admits a total edge irregular s-labeling.
-/

/-- The total edge irregularity strength tes(G) of a simple graph G is the minimum positive integer s admitting a total edge irregular s-labeling. -/
noncomputable def total_edge_irregularity_strength {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {s : ℕ | 0 < s ∧ ∃ (φ : V → ℕ) (ψ : G.edgeSet → ℕ), is_total_edge_irregular_labeling G s φ ψ}
