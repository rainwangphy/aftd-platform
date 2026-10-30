import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointFirstBlock
import AFTD.Kb.Tcs.WildJointBlock
import AFTD.Kb.Tcs.WildJointBadRelation
import AFTD.Kb.Tcs.WildJointCanonicalMatching

/-!
# wild_joint_alpha

Topic: graphs   Node: fc1bfffe46f8

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

alpha(T): the conditional probability, under the uniform distribution on all vertex permutations σ, that the fixed canonical matching is whole-bad for the block map of σ, given that the first block equals T. Defined as an explicit ratio of finite cardinalities (the conditioning event has 6*(n-3)! elements when |T|=3).
-/

/-- alpha(T) = P(canonical matching whole-bad | first block = T), as a cardinality ratio. -/
noncomputable def wild_joint_alpha (q : ℕ) (T : Finset (Fin (3*q))) : ℝ := by classical exact ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ = T ∧ wild_joint_bad_relation q (wild_joint_block q σ) (wild_joint_canonical_matching q))).card : ℝ) / ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ = T)).card : ℝ)
