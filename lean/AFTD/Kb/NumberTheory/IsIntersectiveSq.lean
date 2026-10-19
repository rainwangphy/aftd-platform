import AFTD.Prelude

/-!
# is_intersective_sq

Topic: elementary_number_theory   Node: c84ca621b61c

Provenance: helper lemma. folklore

The polynomial $X^2$ has an integer root modulo every positive integer $m$.
-/

/-- The polynomial X^2 has a root modulo every positive integer m. -/
theorem is_intersective_sq : ∀ m : ℕ, 0 < m → ∃ n : ℤ, (Polynomial.X ^ 2 : Polynomial ℤ).eval n ≡ 0 [ZMOD m] := by
  intro m _
  exact ⟨0, by simp⟩
