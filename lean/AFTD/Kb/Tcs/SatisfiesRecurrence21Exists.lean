import AFTD.Prelude
import AFTD.Kb.Tcs.SatisfiesRecurrence21

/-!
# satisfies_recurrence_2_1_exists

Topic: combinatorics   Node: 5ac0906ad39d

Provenance: helper lemma. arXiv:2611.01561, Section 2

For every integer N ≥ 1, there exist recurrence coefficients a, b, c : Fin (N + 1) → ℝ satisfying condition (2.1).
-/

/-- Sanity lemma: existence of coefficients satisfying condition (2.1) for every N ≥ 1. -/
theorem satisfies_recurrence_2_1_exists (N : ℕ) (hN : 1 ≤ N) :
    ∃ a b c : Fin (N + 1) → ℝ, satisfies_recurrence_2_1 N a b c := by
  let a : Fin (N + 1) → ℝ := fun i => if (i : ℕ) < N then 1 else 0
  let c : Fin (N + 1) → ℝ := fun i => if (i : ℕ) = 0 then 0 else 1
  let b : Fin (N + 1) → ℝ := fun i => 1 - a i - c i
  use a, b, c
  dsimp [satisfies_recurrence_2_1]
  have h0N : 0 < N := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a, h0N]
  · simp [b, a, c, h0N]
  · simp [c]
  · simp [a]
  · intro i
    simp only [b]
    ring
  · intro i hi
    simp [a, hi]
  · intro i hi
    dsimp [c]
    split_ifs with h
    · omega
    · norm_num
