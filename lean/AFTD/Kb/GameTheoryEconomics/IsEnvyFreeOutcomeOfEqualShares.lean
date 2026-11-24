import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeOutcome

/-!
# is_envy_free_outcome_of_equal_shares

Topic: social_choice   Node: 29aafe4be559

Provenance: helper lemma. folklore

For n parties with equal vote shares heq : ∀ i j, p i = p j and house size h, every subset S of additional seats is envy-free.
-/

open Classical in
/-- Equal vote shares imply that every outcome of extra seats is envy-free. -/
theorem is_envy_free_outcome_of_equal_shares {n : ℕ} (p : Fin n → ℝ) (h : ℕ) (S : Finset (Fin n))
    (heq : ∀ i j, p i = p j) : is_envy_free_outcome p h S := by
  intro i j hlt
  have := heq j i
  rw [this] at hlt
  exact False.elim (lt_irrefl (p i) hlt)
