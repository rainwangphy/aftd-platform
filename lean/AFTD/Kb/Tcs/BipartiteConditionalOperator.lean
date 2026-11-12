import AFTD.Prelude

/-!
# bipartite_conditional_operator

Topic: quantum   Node: 15eaf2ab1fea

Provenance: helper lemma. step towards ppt_qutrit_steered_effect_is_valid

The (unnormalized) conditional operator on the second system β of a bipartite matrix ρ produced by the operator M on the first system: (condOp ρ M) x y = ∑_a ∑_b ρ (a,x) (b,y) * M b a.
-/

/-- The unnormalized conditional operator on the second factor of a bipartite matrix. -/
noncomputable def bipartite_conditional_operator {α β : Type} [Fintype α] [Fintype β] (ρ : Matrix (α × β) (α × β) ℂ) (M : Matrix α α ℂ) : Matrix β β ℂ := fun x y => ∑ a, ∑ b, ρ (a, x) (b, y) * M b a
