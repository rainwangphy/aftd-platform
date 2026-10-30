import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointBlockSet

/-!
# wild_joint_invalid_count

Topic: graphs   Node: b3984921ad6a

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

I(σ): the number of colours i that invalidate a triple block, i.e. there exist distinct x,y in a single σ-block with A x y = i and i in that same block. Each colour can invalidate at most one block (the block containing i), so I = sum over blocks b of mu(block_b).
-/

/-- I(σ): number of colours invalidating a triple block. -/
noncomputable def wild_joint_invalid_count (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (σ : Equiv.Perm (Fin (3*q))) : ℕ := by classical exact (Finset.univ.filter (fun i : Fin (3*q) => ∃ b : Fin q, i ∈ wild_joint_block_set q σ b ∧ ∃ x ∈ wild_joint_block_set q σ b, ∃ y ∈ wild_joint_block_set q σ b, x ≠ y ∧ A x y = i)).card
