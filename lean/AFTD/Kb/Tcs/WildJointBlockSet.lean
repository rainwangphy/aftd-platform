import AFTD.Prelude

/-!
# wild_joint_block_set

Topic: graphs   Node: 9a2f0de37256

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

The b-th block as a vertex set = {σ (3b), σ (3b+1), σ (3b+2)}. Note wild_joint_block_set q σ 0 = wild_joint_first_block q σ.
-/

/-- b-th block as a vertex set. -/
noncomputable def wild_joint_block_set (q : ℕ) (σ : Equiv.Perm (Fin (3*q))) (b : Fin q) : Finset (Fin (3*q)) := Finset.univ.filter (fun v => (σ.symm v).val / 3 = b.val)
