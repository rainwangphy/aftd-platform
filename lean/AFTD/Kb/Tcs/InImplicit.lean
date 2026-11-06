import AFTD.Prelude

/-!
# InImplicit

Topic: combinatorics   Node: 230c584ae33b

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 2.1

For a diagram given as a finite set D : Finset (ℕ × ℕ), a cell (i, j) : ℕ × ℕ is in the implicit closure InImplicit D (i, j) if it belongs to D, or lies in the same row weakly between two cells in the closure (with row i and column j₁ ≤ j ≤ j₂), or lies in the same column weakly between two cells in the closure (with column j and row i₁ ≤ i ≤ i₂).
-/

/-- Predicate for cells in the smallest set containing D closed under row and column betweenness (implicit boxes). -/
inductive InImplicit (D : Finset (ℕ × ℕ)) : ℕ × ℕ → Prop | base {x} : x ∈ D → InImplicit D x
| row_between {i j₁ j₂ j} : InImplicit D (i, j₁) → InImplicit D (i, j₂) → j₁ ≤ j → j ≤ j₂ → InImplicit D (i, j)
| col_between {i₁ i₂ j i} : InImplicit D (i₁, j) → InImplicit D (i₂, j) → i₁ ≤ i → i ≤ i₂ → InImplicit D (i, j)
