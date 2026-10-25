import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMonochromaticEdges
import AFTD.Kb.Tcs.SimpleGraphIsFarColorable
import AFTD.Kb.Tcs.SimpleGraphDeleteMonochromaticEdgesColorable
import AFTD.Kb.Tcs.SimpleGraphExistsMonochromaticEdgesSubsetOfDeleteEdgesColorable
import AFTD.Kb.Tcs.SimpleGraphMonochromaticEdgesSubset

/-!
# simple_graph_is_far_colorable_iff

Topic: combinatorics   Node: ec8d93594b51

Provenance: formalization of a published result. Source: combinatorics/2610-31489-near-optimal-bounds-for-testing-k-colorability.md:152

A finite simple graph G on a type V with decidable equality and decidable adjacency is ε-far from being k-colorable if and only if every vertex coloring c : V → Fin k satisfies ε * (Fintype.card V : ℝ) ^ 2 ≤ ((simple_graph_monochromatic_edges G c).card : ℝ).
-/

/-- A graph G is ε-far from being k-colorable if and only if every vertex coloring c : V → Fin k has at least ε |V|² monochromatic edges. -/
theorem simple_graph_is_far_colorable_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (ε : ℝ) :
    simple_graph_is_far_colorable G k ε ↔
      ∀ c : V → Fin k, ε * (Fintype.card V : ℝ) ^ 2 ≤ ((simple_graph_monochromatic_edges G c).card : ℝ) := by
  constructor
  · intro h c
    have hsub : simple_graph_monochromatic_edges G c ⊆ G.edgeFinset :=
      simple_graph_monochromatic_edges_subset G c
    have hcol : (G.deleteEdges (simple_graph_monochromatic_edges G c : Set (Sym2 V))).Colorable k :=
      simple_graph_delete_monochromatic_edges_colorable G c
    exact h (simple_graph_monochromatic_edges G c) hsub hcol
  · intro h E' hsub hcol
    rcases simple_graph_exists_monochromatic_edges_subset_of_delete_edges_colorable G hcol with ⟨c, hc⟩
    have hle : ((simple_graph_monochromatic_edges G c).card : ℝ) ≤ (E'.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hc
    exact le_trans (h c) hle
