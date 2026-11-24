import AFTD.Prelude
import AFTD.Kb.Tcs.MaximalChainLowerSet
import AFTD.Kb.Tcs.Order

/-!
# maximal_chain_map_automorphism

Topic: combinatorics   Node: 3869bf4a3288

Provenance: formalization of a published result. Source: arXiv:2611.26888 Proposition 3.3

Given an order automorphism f : P ≃o P of a finite partially ordered set P and a maximal chain M : MaximalChainLowerSet P of order ideals, maximal_chain_map_automorphism f M is the maximal chain of order ideals whose j-th ideal is LowerSet.map f.symm (M.chain j).
-/

/-- The action of a poset automorphism on maximal chains of order ideals. -/
def maximal_chain_map_automorphism {P : Type*} [PartialOrder P] [Fintype P]
    (f : P ≃o P) (M : MaximalChainLowerSet P) : MaximalChainLowerSet P := ⟨fun j => LowerSet.map f.symm (M.chain j),
   by rw [M.bot_eq]; exact OrderIso.map_bot _,
   by rw [M.top_eq]; exact OrderIso.map_top _,
   fun i => (apply_covBy_apply_iff (LowerSet.map f.symm)).mpr (M.covBy i)⟩
