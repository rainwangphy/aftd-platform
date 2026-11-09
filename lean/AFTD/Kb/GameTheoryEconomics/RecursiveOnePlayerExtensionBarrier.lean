import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RecursiveOnePlayerExtensionReciprocal

/-!
# recursive_one_player_extension_barrier

Topic: equilibria   Node: 631581d44e84

Provenance: formalization of a published result. Source: arXiv:2611.06076 Proposition 2.3

Let r be a natural number and let α : ℕ → ℝ be a sequence satisfying 0 ≤ α r and α r < 1. Under the one-player extension recurrence α (k + 1) = 1 / (2 - α k) for all k ≥ r, the approximation guarantee for any m ≥ r satisfies α m = 1 - 1 / ((m : ℝ) - c), where c = (r : ℝ) - 1 / (1 - α r).
-/

/-- Proposition 2.3: Limitation of recursive one-player extension for multiplayer approximate Nash equilibria. -/
theorem recursive_one_player_extension_barrier
    (r : ℕ) (α : ℕ → ℝ) (hαr : 0 ≤ α r ∧ α r < 1)
    (hrec : ∀ k, r ≤ k → α (k + 1) = 1 / (2 - α k))
    (m : ℕ) (hm : r ≤ m) :
    let c : ℝ := (r : ℝ) - 1 / (1 - α r)
    α m = 1 - 1 / ((m : ℝ) - c) := by
  have h := recursive_one_player_extension_reciprocal r α hαr.2 hrec m hm
  have hc : (m : ℝ) - ((r : ℝ) - 1 / (1 - α r)) = 1 / (1 - α m) := by
    rw [h]; ring
  show α m = 1 - 1 / ((m : ℝ) - ((r : ℝ) - 1 / (1 - α r)))
  rw [hc]
  have hinv : 1 / (1 / (1 - α m)) = 1 - α m := by
    rw [one_div_div]; simp
  rw [hinv]; ring
