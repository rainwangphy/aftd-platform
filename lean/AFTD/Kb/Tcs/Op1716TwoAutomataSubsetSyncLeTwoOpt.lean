import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSimultaneouslySynchronizing
import AFTD.Kb.Tcs.DfaIsSeqSubsetSyncChoice
import AFTD.Kb.Tcs.DfaSeqSubsetSyncTotalLeKMulSimultaneous

/-!
# op_1716_two_automata_subset_sync_le_two_opt

Topic: automata   Node: a0722d7b5dc4

Provenance: formalization of a published result. Source: arXiv:2611.09136

For any two deterministic finite automata A (k = 2) and any two-stage sequential subset synchronization choice ws, the total length (ws 0).length + (ws 1).length is at most 2 * w_opt.length for any simultaneously synchronizing word w_opt.
-/

/-- For two deterministic finite automata, the total length of a two-stage sequential subset synchronization choice is at most twice the length of any simultaneously synchronizing word. -/
theorem op_1716_two_automata_subset_sync_le_two_opt {α : Type*} {σ : Fin 2 → Type*}
    (A : (i : Fin 2) → DFA α (σ i)) (ws : Fin 2 → List α)
    (h_choice : dfa_is_seq_subset_sync_choice A ws)
    (w_opt : List α) (h_opt : dfa_is_simultaneously_synchronizing A w_opt) :
    (ws 0).length + (ws 1).length ≤ 2 * w_opt.length := by
  have h := dfa_seq_subset_sync_total_le_k_mul_simultaneous A ws h_choice w_opt h_opt
  simpa [Fin.sum_univ_two] using h
