import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnePlayerExtensionReciprocalStep
import AFTD.Kb.GameTheoryEconomics.RecursiveOnePlayerExtensionLtOne

/-!
# recursive_one_player_extension_reciprocal

Topic: equilibria   Node: 38d9b68fb52e

Provenance: helper lemma. arXiv:2611.06076 Proposition 2.3 proof

Let r be a natural number, and let α : ℕ → ℝ be a sequence satisfying α (k + 1) = 1 / (2 - α k) for all k ≥ r. If α r < 1, then for all m ≥ r, 1 / (1 - α m) = 1 / (1 - α r) + ((m : ℝ) - (r : ℝ)).
-/

/-- Telescoping sum of reciprocals for the one-player extension recurrence. -/
lemma recursive_one_player_extension_reciprocal
    (r : ℕ) (α : ℕ → ℝ) (hαr : α r < 1)
    (hrec : ∀ k, r ≤ k → α (k + 1) = 1 / (2 - α k))
    (m : ℕ) (hm : r ≤ m) :
    1 / (1 - α m) = 1 / (1 - α r) + ((m : ℝ) - (r : ℝ)) := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      rw [hrec m hm]
      rw [one_player_extension_reciprocal_step (α m)
        (recursive_one_player_extension_lt_one r α hαr hrec m hm)]
      rw [ih]
      push_cast
      ring
