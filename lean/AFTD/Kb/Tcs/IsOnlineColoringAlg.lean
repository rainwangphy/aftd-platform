import AFTD.Prelude

/-!
# IsOnlineColoringAlg

Topic: online_algorithms   Node: 2dcd488dbe5a

Provenance: formalization of a published result. Source: arXiv:2610.41516 Section 1

A deterministic coloring algorithm A : SimpleGraph (Fin n) → (Fin n → ℕ) assigning natural number colors to vertices of graphs on Fin n is online (causal) if for any two graphs G₁ and G₂ and any vertex i : Fin n, if for all j, l ≤ i we have G₁.Adj j l ↔ G₂.Adj j l, then A G₁ i = A G₂ i.
-/

/-- A deterministic vertex coloring algorithm on Fin n assigning natural number colors is online if the color of vertex i depends only on edges between vertices up to index i. -/
def IsOnlineColoringAlg {n : ℕ} (A : SimpleGraph (Fin n) → (Fin n → ℕ)) : Prop :=
  ∀ (G₁ G₂ : SimpleGraph (Fin n)) (i : Fin n),
    (∀ j l : Fin n, j ≤ i → l ≤ i → (G₁.Adj j l ↔ G₂.Adj j l)) → A G₁ i = A G₂ i
