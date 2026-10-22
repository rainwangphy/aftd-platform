import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLeSmall
import AFTD.Kb.Tcs.TarskiBoxQueryLe

/-!
# tarski_box_query_le_two_five

Topic: algorithms   Node: 6f4711522bfd

Provenance: helper lemma. step towards tarski_box_query_le_five_log_sq

Small instance at the exact target parameters: in dimension 5 over the two-element grid, every box is solvable with at most 2^5 = 32 queries. Consequently the box invariant of the open target is inhabited at (n, k) = (2, 5), and any constant in the target must be at least 32.
-/

/-- Non-vacuity witness at the target parameters: the box invariant is satisfiable in dimension 5 with 32 = 2^5 queries when n = 2, so the target's constant must satisfy C ≥ 32. -/
theorem tarski_box_query_le_two_five : tarski_box_query_le 2 5 32 := by
  apply tarski_box_query_le_small 2 5 32
  intro a b _hab
  have h1 : ∀ j : Fin 5, ((b j : ℕ) - (a j : ℕ) + 1) ≤ (2 : ℕ) := by
    intro j
    have : (b j : ℕ) < 2 := (b j).isLt
    omega
  have h2 : (∏ j : Fin 5, ((b j : ℕ) - (a j : ℕ) + 1)) ≤ ∏ _ : Fin 5, (2 : ℕ) := by
    apply Finset.prod_le_prod
    · intro j _hj
      omega
    · intro j _hj
      exact h1 j
  have h3 : (∏ _ : Fin 5, (2 : ℕ)) = 32 := by
    decide
  exact h2.trans_eq h3
