import AFTD.Prelude

/-!
# nfa_run_count_list

Topic: automata   Node: 573609232c75

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

The number of runs of the word w in the NFA M from state p to state q: state sequences of length |w|+1 that start at p, end at q and follow the transitions.
-/

/-- The number of runs of the word w in the NFA M from state p to state q. -/
noncomputable def nfa_run_count_list {α σ : Type*} [Fintype σ] (M : NFA α σ) (w : List α) (p q : σ) : ℕ := {r : Fin (w.length + 1) → σ |
    r 0 = p ∧ r (Fin.last w.length) = q ∧
      ∀ i : Fin w.length, r i.succ ∈ M.step (r i.castSucc) (w.get i)}.ncard
