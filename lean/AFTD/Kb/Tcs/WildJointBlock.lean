import AFTD.Prelude

/-!
# wild_joint_block

Topic: graphs   Node: ecca7ff943b5

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

Block (index of the consecutive triple) containing vertex v under the permutation σ, where σ p is the vertex at position p; blocks are positions {3b,3b+1,3b+2}.
-/

/-- Block index of v in σ-order: (position of v) / 3. -/
noncomputable def wild_joint_block (q : ℕ) (σ : Equiv.Perm (Fin (3*q))) (v : Fin (3*q)) : Fin q := ⟨(σ.symm v).val / 3, by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; have := (σ.symm v).isLt; omega⟩
