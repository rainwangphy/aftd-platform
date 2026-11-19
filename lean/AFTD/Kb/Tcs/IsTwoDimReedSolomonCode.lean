import AFTD.Prelude

/-!
# is_two_dim_reed_solomon_code

Topic: information   Node: 4cd82174c13b

Provenance: formalization of a published result. Source: arXiv:2611.21275 Definition 5

For any field $F$ and any $F$-submodule $C$ of $\mathrm{Fin}\,n \to F$, $C$ is a two-dimensional Reed-Solomon code if there exists an injective function $\alpha : \mathrm{Fin}\,n \to F$ such that $C$ equals the $F$-submodule spanned by the set containing the all-ones vector and $\alpha$.
-/

/-- Predicate stating that a linear code over a field F is a two-dimensional Reed-Solomon code. -/
def is_two_dim_reed_solomon_code {n : ℕ} {F : Type*} [Field F]
    (C : Submodule F (Fin n → F)) : Prop := ∃ α : Fin n → F, Function.Injective α ∧ C = Submodule.span F {fun _ => (1 : F), α}
