import AFTD.Prelude
import AFTD.Kb.Tcs.Op309GraphFourDegenerate
import AFTD.Kb.Tcs.Op309PaddedPortValidGraphHom
import AFTD.Kb.Tcs.Op309PaddedAlmostStarPortGraphValid

/-!
# op309_complete_five_four_degenerate

Topic: graphs   Node: fa653f28b829

Provenance: helper lemma. OP-309 padded port-class selection, IN-1099.

The complete graph on five vertices is four-degenerate.
-/

theorem op309_complete_five_four_degenerate:
    op309_graph_four_degenerate (⊤ : SimpleGraph (Fin 5)) := by
  intro S hS
  obtain ⟨v, hv⟩ := hS
  refine ⟨v, hv, Finset.univ.erase v, ?_, ?_⟩
  · simp
  · intro w hw hadj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact Ne.symm hadj
