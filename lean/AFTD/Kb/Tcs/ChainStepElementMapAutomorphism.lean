import AFTD.Prelude
import AFTD.Kb.Tcs.ChainStepElement
import AFTD.Kb.Tcs.MaximalChainMapAutomorphism
import AFTD.Kb.Tcs.MaximalChainLowerSet

/-!
# chain_step_element_map_automorphism

Topic: combinatorics   Node: de23a12811c5

Provenance: formalization of a published result. Source: arXiv:2611.26888 Lemma 3.4

Let P be a finite partially ordered set with poset automorphism f : P ≃o P. For any maximal chain M : MaximalChainLowerSet P of order ideals, index i : Fin (Fintype.card P), and element x : P, chain_step_element M i x holds if and only if chain_step_element (maximal_chain_map_automorphism f M) i (f.symm x) holds.
-/

/-- Poset automorphisms preserve the step elements of maximal chains of order ideals. -/
theorem chain_step_element_map_automorphism {P : Type*} [PartialOrder P] [Fintype P]
    (f : P ≃o P) (M : MaximalChainLowerSet P) (i : Fin (Fintype.card P)) (x : P) :
    chain_step_element M i x ↔
      chain_step_element (maximal_chain_map_automorphism f M) i (f.symm x) := by
  simp [chain_step_element, maximal_chain_map_automorphism]
