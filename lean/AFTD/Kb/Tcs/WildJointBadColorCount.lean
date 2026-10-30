import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointBadRelation
import AFTD.Kb.Tcs.WildJointBlock

/-!
# wild_joint_bad_color_count

Topic: graphs   Node: 42b818f7580a

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

D(σ): the number of colours i that are whole-bad, i.e. some proper union of σ-blocks has no colour-i edge crossing it (block graph of the colour-i matching is disconnected).
-/

/-- D(σ): number of whole-bad colours. -/
noncomputable def wild_joint_bad_color_count (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (σ : Equiv.Perm (Fin (3*q))) : ℕ := by classical exact (Finset.univ.filter (fun i : Fin (3*q) => wild_joint_bad_relation q (wild_joint_block q σ) (fun x y => x ≠ y ∧ A x y = i))).card
