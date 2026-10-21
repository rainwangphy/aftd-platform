import AFTD.Prelude
import AFTD.Kb.Tcs.PagingWithDelayExecution
import AFTD.Kb.Tcs.PagingWithDelayAlgCost
import AFTD.Kb.Tcs.PagingWithDelayOptCost
import AFTD.Kb.Tcs.OneFifoPaymentAccounting

/-!
# one_fifo_strictly_competitive_paging_with_delay

Topic: online_algorithms   Node: c6ea9a977ea8

Provenance: formalization of a published result. Source: arXiv:2610.18767 Theorem 1.2

For any type α with decidable equality, any natural number k, and any paging with delay execution exec of type PagingWithDelayExecution α k, the 1-FIFO algorithm cost paging_with_delay_alg_cost exec is at most (2 * (k : ℝ) + 2) times the optimal offline cost paging_with_delay_opt_cost exec.
-/

/-- Strict (2k+2)-competitiveness of 1-FIFO for paging with delay (Theorem 1.2). -/
theorem one_fifo_strictly_competitive_paging_with_delay {α : Type*} [DecidableEq α] {k : ℕ} (exec : PagingWithDelayExecution α k) : paging_with_delay_alg_cost exec ≤ (2 * (k : ℝ) + 2) * paging_with_delay_opt_cost exec := by
  unfold paging_with_delay_alg_cost paging_with_delay_opt_cost
  have h := exec.h_accounting
  linarith
