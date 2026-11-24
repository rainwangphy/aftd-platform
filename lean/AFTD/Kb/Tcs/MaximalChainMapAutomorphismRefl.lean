import AFTD.Prelude
import AFTD.Kb.Tcs.MaximalChainMapAutomorphism
import AFTD.Kb.Tcs.MaximalChainLowerSet

/-!
# maximal_chain_map_automorphism_refl

Topic: combinatorics   Node: b3dfd2f987ee

Provenance: helper lemma. arXiv:2611.26888 Proposition 3.3

The identity order automorphism of a finite partially ordered set P acts trivially on any maximal chain of order ideals M of type MaximalChainLowerSet P under maximal_chain_map_automorphism.
-/

/-- The identity automorphism acts trivially on maximal chains of order ideals. -/
theorem maximal_chain_map_automorphism_refl {P : Type*} [PartialOrder P] [Fintype P]
    (M : MaximalChainLowerSet P) :
    maximal_chain_map_automorphism (OrderIso.refl P) M = M := by
  simp [maximal_chain_map_automorphism]
