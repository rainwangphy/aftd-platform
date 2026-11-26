import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DigraphKInducible

/-!
# digraph_k_inducible_three_cycle

Topic: social_choice   Node: 27254428cef7

Provenance: helper lemma. Sanity lemma for digraph_k_inducible (OP-2174, arXiv:2611.27965): the Condorcet profile induces the 3-cycle

The directed 3-cycle 0 → 1 → 2 → 0 on Fin 3 is 3-inducible (the Condorcet cycle of three voters).
-/

theorem digraph_k_inducible_three_cycle :
    digraph_k_inducible 3 (⟨fun a b => b = a + 1⟩ : Digraph (Fin 3)) := by
  refine ⟨![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]], by decide, ?_⟩
  decide
