import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteGraphLineGraphColorable
import AFTD.Kb.Tcs.CompleteGraphOddLineGraphLeChromaticNumber

/-!
# complete_graph_odd_line_graph_chromatic_number_eq

Topic: graphs   Node: 83f04ae230a0

Provenance: helper lemma. Standard complete-graph edge-coloring fact used by arXiv:2610.22142, Section 3, and needed for the proposed OP-306 permutation-event normalization.

The edge chromatic number of an odd complete graph on at least three vertices is its number of vertices.
-/

theorem complete_graph_odd_line_graph_chromatic_number_eq (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = n := by
  exact le_antisymm (complete_graph_line_graph_colorable n hn).chromaticNumber_le
    (complete_graph_odd_line_graph_le_chromaticNumber n hn hodd)
