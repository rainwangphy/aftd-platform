import AFTD.Prelude
import AFTD.Kb.Tcs.PagingWithDelayExecution

/-!
# paging_with_delay_opt_cost

Topic: online_algorithms   Node: 5e95d0cf9ec8

Provenance: formalization of a published result. Source: arXiv:2610.18767 Section 2, line 300

The total offline cost in a paging with delay execution exec, defined as the sum of offline fetches and offline delay: (exec.F_opt : ℝ) + exec.D_opt.
-/

/-- Total cost of offline algorithm: fetches plus delay. -/
def paging_with_delay_opt_cost {α : Type*} [DecidableEq α] {k : ℕ} (exec : PagingWithDelayExecution α k) : ℝ := (exec.F_opt : ℝ) + exec.D_opt
