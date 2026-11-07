import AFTD.Prelude

/-!
# is_graceful_tree

Topic: graphs   Node: 064950e15832

Provenance: formalization of a published result. Source: arXiv:2611.01340 Section 1; Golomb 1972

A tree G on a finite vertex type W is graceful if there exists a bijection f : W ≃ Fin (Fintype.card W) such that for all edges {u₁, v₁} and {u₂, v₂} of G, if the edge differences |f(u₁) - f(v₁)| and |f(u₂) - f(v₂)| are equal, then {u₁, v₁} = {u₂, v₂}.
-/

/-- A tree G on a finite vertex type is graceful if there exists a bijection f from its vertices to {0, ..., |W|-1} such that the edge differences |f(u) - f(v)| are pairwise distinct for all edges of G. -/
def is_graceful_tree {W : Type*} [Fintype W] (G : SimpleGraph W) : Prop := G.IsTree ∧ ∃ f : W ≃ Fin (Fintype.card W),
    ∀ ⦃u₁ v₁ u₂ v₂ : W⦄, G.Adj u₁ v₁ → G.Adj u₂ v₂ →
      Nat.dist (f u₁) (f v₁) = Nat.dist (f u₂) (f v₂) → s(u₁, v₁) = s(u₂, v₂)
