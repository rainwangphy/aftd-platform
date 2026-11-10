import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.HasWinningStrategyInMem
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.FiniteMemoryStrategy

/-!
# has_winning_strategy_in_mem_mono

Topic: automata   Node: 792327498a21

Provenance: helper lemma. step towards op_1385_three_priority_borel_finite_memory_determinacy

In any prioritized Borel game G with k priorities on state space Q, if a player has a winning strategy using at most m1 memory states, and m1 ≤ m2, then the player has a winning strategy using at most m2 memory states.
-/

/-- A winning strategy using at most m1 memory states also uses at most m2 memory states whenever m1 ≤ m2. -/
theorem has_winning_strategy_in_mem_mono {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k) {m1 m2 : ℕ} (h : m1 ≤ m2) (hw : HasWinningStrategyInMem G m1) : HasWinningStrategyInMem G m2 := by
  rcases hw with ⟨pl, M, fM, hcard, strat, hwin⟩
  exact ⟨pl, M, fM, hcard.trans h, strat, hwin⟩
