import AFTD.Prelude
import AFTD.Kb.Tcs.NfaRunCountFiberwiseSum
import AFTD.Kb.Tcs.NfaRunPenultimateFiber
import AFTD.Kb.Tcs.NfaRunCountList

/-!
# nfa_run_count_list_concat

Topic: automata   Node: b3c7b5cd799c

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

Number of runs on w++[a] from p to q equals the sum over s of the number of runs on w from p to s, taken over the predecessors s of q on letter a.
-/

open Classical in
/-- Appending one letter distributes a run count over the possible previous state. -/
theorem nfa_run_count_list_concat {α σ : Type*} [Fintype σ] (M : NFA α σ) (w : List α) (a : α)
    (p q : σ) :
    nfa_run_count_list M (w ++ [a]) p q
      = ∑ s : σ, if q ∈ M.step s a then nfa_run_count_list M w p s else 0 := by
  rw [nfa_run_count_fiberwise_sum]
  simp_rw [nfa_run_penultimate_fiber]
