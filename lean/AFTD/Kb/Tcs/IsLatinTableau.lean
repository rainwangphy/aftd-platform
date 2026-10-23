import AFTD.Prelude

/-!
# is_latin_tableau

Topic: combinatorics   Node: 807aa37d01ac

Provenance: formalization of a published result. Source: arXiv:2610.29291 Definition 2.5

A filling $T$ of a Young diagram $\lambda$ is a Latin tableau of shape $\lambda$ and type $\lambda'$ if each row $i$ contains entries from $1$ through $\lambda_i$ without repetition, and no entry repeats within any column.
-/

/-- Predicate stating that T is a Latin tableau of shape μ and type conjugate of μ. -/
def is_latin_tableau (μ : YoungDiagram) (T : ℕ → ℕ → ℕ) : Prop := (∀ {i j}, (i, j) ∈ μ → 1 ≤ T i j ∧ T i j ≤ μ.rowLen i) ∧
  (∀ {i j₁ j₂}, (i, j₁) ∈ μ → (i, j₂) ∈ μ → T i j₁ = T i j₂ → j₁ = j₂) ∧
  (∀ {i₁ i₂ j}, (i₁, j) ∈ μ → (i₂, j) ∈ μ → T i₁ j = T i₂ j → i₁ = i₂)
