import AFTD.Prelude

/-!
# array_col_frequency

Topic: combinatorics   Node: 165de5bfe82f

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 2

The column frequency f(c) of a column c in a δ × δ array with filled cells Δ is the number of filled cells in column c.
-/

/-- The number of filled cells in column c of an array with filled cells Δ. -/
def array_col_frequency {δ : ℕ} (Δ : Finset (Fin δ × Fin δ)) (c : Fin δ) : ℕ :=
  ((Finset.univ : Finset (Fin δ)).filter (fun r => (r, c) ∈ Δ)).card
