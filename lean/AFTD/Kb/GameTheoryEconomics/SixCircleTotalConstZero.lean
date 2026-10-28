import AFTD.Prelude

/-!
# six_circle_total_const_zero

Topic: combinatorial_games   Node: ee3ded485e7d

Provenance: helper lemma. folklore

Under the constant zero protocol, the total number of 1s in any circular seating π of six sages is 0.
-/

/-- Sanity lemma: the constant zero protocol yields a total of 0 in every seating. -/
theorem six_circle_total_const_zero (π : Equiv.Perm (Fin 6)) :
    ∑ i : Fin 6, ((fun _ : Fin 6 × Fin 6 × Fin 6 × Fin 6 => (0 : Fin 2)) (π i, i, π (i - 1), π (i + 1)) : ℕ) = 0 := by
  simp
