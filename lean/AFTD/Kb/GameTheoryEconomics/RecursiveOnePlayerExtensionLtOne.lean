import AFTD.Prelude

/-!
# recursive_one_player_extension_lt_one

Topic: equilibria   Node: 3d2e293fe400

Provenance: helper lemma. arXiv:2611.06076 Proposition 2.3 proof

Let r be a natural number, and let α : ℕ → ℝ be a sequence satisfying α (k + 1) = 1 / (2 - α k) for all k ≥ r. If α r < 1, then for all m ≥ r, α m < 1.
-/

/-- Under the one-player extension recurrence with initial value strictly less than 1, all subsequent values remain strictly less than 1. -/
lemma recursive_one_player_extension_lt_one
    (r : ℕ) (α : ℕ → ℝ) (hαr : α r < 1)
    (hrec : ∀ k, r ≤ k → α (k + 1) = 1 / (2 - α k))
    (m : ℕ) (hm : r ≤ m) :
    α m < 1 := by
  have hstep : ∀ k, r ≤ k → α k < 1 → α (k + 1) < 1 := by
    intro k hk hlt
    rw [hrec k hk]
    have hpos : 0 < 2 - α k := by linarith
    rw [div_lt_one hpos]
    linarith
  exact Nat.le_induction hαr (fun k hk ih => hstep k hk ih) m hm
