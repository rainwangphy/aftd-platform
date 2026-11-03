import AFTD.Prelude

/-!
# ProperlyColorsKColorable

Topic: online_algorithms   Node: 226f164d0a42

Provenance: formalization of a published result. Source: arXiv:2610.41516 Section 1

For an integer k and graph size n, a coloring algorithm A : SimpleGraph (Fin n) → (Fin n → ℕ) assigning natural number colors properly colors k-colorable graphs if for every simple graph G on Fin n such that G.Colorable k, for all u, v : Fin n, G.Adj u v implies A G u ≠ A G v.
-/

/-- A coloring algorithm on Fin n assigning natural number colors properly colors k-colorable graphs if it gives a proper coloring whenever G is k-colorable. -/
def ProperlyColorsKColorable {n : ℕ} (k : ℕ) (A : SimpleGraph (Fin n) → (Fin n → ℕ)) : Prop :=
  ∀ (G : SimpleGraph (Fin n)), G.Colorable k →
    ∀ (u v : Fin n), G.Adj u v → A G u ≠ A G v
