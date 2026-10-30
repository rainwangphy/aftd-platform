import AFTD.Prelude

/-!
# wild_joint_first_block

Topic: graphs   Node: cea6b1b2cca4

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

The first block: the set of vertices placed in positions 0,1,2 by σ (= {σ 0, σ 1, σ 2}).
-/

/-- First block of σ: vertices at positions 0,1,2. -/
noncomputable def wild_joint_first_block (q : ℕ) (σ : Equiv.Perm (Fin (3*q))) : Finset (Fin (3*q)) := Finset.univ.filter (fun v => (σ.symm v).val < 3)
