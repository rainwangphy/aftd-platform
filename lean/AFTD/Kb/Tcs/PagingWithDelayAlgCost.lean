import AFTD.Prelude
import AFTD.Kb.Tcs.PagingWithDelayExecution

/-!
# paging_with_delay_alg_cost

Topic: online_algorithms   Node: 58714e4f38c4

Provenance: formalization of a published result. Source: arXiv:2610.18767 Observation 3.1

The total cost incurred by the 1-FIFO algorithm in a paging with delay execution exec, defined as 2 * (exec.P : ℝ).
-/

/-- Total cost of 1-FIFO: 2 per payment. -/
def paging_with_delay_alg_cost {α : Type*} [DecidableEq α] {k : ℕ} (exec : PagingWithDelayExecution α k) : ℝ := 2 * (exec.P : ℝ)
