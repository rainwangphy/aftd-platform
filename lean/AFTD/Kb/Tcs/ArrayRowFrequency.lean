import AFTD.Prelude

/-!
# array_row_frequency

Topic: combinatorics   Node: edaa0a67589b

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 2

The row frequency f(r) of a row r in a δ × δ array with filled cells Δ is the number of filled cells in row r.
-/

/-- The number of filled cells in row r of an array with filled cells Δ. -/
def array_row_frequency {δ : ℕ} (Δ : Finset (Fin δ × Fin δ)) (r : Fin δ) : ℕ :=
  ((Finset.univ : Finset (Fin δ)).filter (fun c => (r, c) ∈ Δ)).card
