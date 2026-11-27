import AFTD.Prelude

/-!
# is_separable_bipartite

Topic: quantum   Node: a959dd598ae1

Provenance: formalization of a published result. Source: arXiv:quant-ph/9605038

A bipartite complex matrix ρ on Hilbert space product α × β is separable if there exist vectors x_i on α and y_i on β such that ρ = ∑_i |x_i⟩⟨x_i| ⊗ |y_i⟩⟨y_i|.
-/

/-- A bipartite density operator is separable if it is a convex mixture of product states. -/
def is_separable_bipartite {α β : Type*} (ρ : Matrix (α × β) (α × β) ℂ) : Prop :=
  ∃ (N : ℕ) (x : Fin N → α → ℂ) (y : Fin N → β → ℂ),
    ∀ p q : α × β, ρ p q = ∑ i : Fin N, x i p.1 * star (x i q.1) * (y i p.2 * star (y i q.2))
