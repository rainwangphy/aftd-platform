import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMutualVisibilityChromaticNumber
import AFTD.Kb.Tcs.Graph11
import AFTD.Kb.Tcs.Graph11Diam
import AFTD.Kb.Tcs.Graph11ChromaticNumber
import AFTD.Kb.Tcs.Graph11MutualVisibilityChromaticNumberEqThree

/-!
# exists_diameter_two_graph_mutual_visibility_chromatic_number_three

Topic: graphs   Node: 7cec4888f284

Provenance: formalization of a published result. Source: arXiv:2610.39430, Theorem 3.4

There exists a finite connected simple graph G of diameter 2 such that the mutual-visibility chromatic number of G equals 3 and the chromatic number of G equals 3.
-/

/-- Existence of a diameter-two graph with mutual-visibility chromatic number and chromatic number both equal to 3. -/
theorem exists_diameter_two_graph_mutual_visibility_chromatic_number_three :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.diam = 2 ∧
      graph_mutual_visibility_chromatic_number G = 3 ∧
      G.chromaticNumber = 3 := by
  refine ⟨Fin 11, inferInstance, graph_11, Classical.decRel _,
    SimpleGraph.connected_iff_diam_ne_zero.2 (by rw [graph_11_diam]; norm_num), graph_11_diam,
    graph_11_mutual_visibility_chromatic_number_eq_three.1, graph_11_chromatic_number⟩
