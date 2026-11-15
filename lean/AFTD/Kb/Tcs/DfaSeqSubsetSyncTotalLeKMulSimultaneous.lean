import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSimultaneouslySynchronizing
import AFTD.Kb.Tcs.DfaIsSeqSubsetSyncChoice
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.DfaIsSubsetSynchronizing
import AFTD.Kb.Tcs.DfaSubsetResetThreshold

/-!
# dfa_seq_subset_sync_total_le_k_mul_simultaneous

Topic: automata   Node: 94b033ed91dc

Provenance: formalization of a published result. Source: arXiv:2611.09136

For any family of k deterministic finite automata A and any sequential subset synchronization choice ws, the total length ∑ i, (ws i).length is at most k times the length of any simultaneously synchronizing word w_opt.
-/

/-- The total length of words in any sequential subset synchronization choice for k automata is at most k times the length of any simultaneously synchronizing word. -/
theorem dfa_seq_subset_sync_total_le_k_mul_simultaneous {α : Type*} {k : ℕ} {σ : Fin k → Type*}
    (A : (i : Fin k) → DFA α (σ i)) (ws : Fin k → List α)
    (h_choice : dfa_is_seq_subset_sync_choice A ws)
    (w_opt : List α) (h_opt : dfa_is_simultaneously_synchronizing A w_opt) :
    (∑ i : Fin k, (ws i).length) ≤ k * w_opt.length := by
  have h_le : ∀ i : Fin k, (ws i).length ≤ w_opt.length := by
    intro i
    have h_opt_i : dfa_is_synchronizing (A i) w_opt := h_opt i
    have h_sub : dfa_is_subset_synchronizing (A i)
      (Set.range (fun q : σ i => (A i).evalFrom q (((List.ofFn ws).take i.val).flatten))) w_opt := by
      intro q₁ _ q₂ _
      exact h_opt_i q₁ q₂
    have h_len_eq := (h_choice i).2
    have h_mem : (w_opt.length : WithTop ℕ) ∈ (fun w : List α => (w.length : WithTop ℕ)) ''
      { w | dfa_is_subset_synchronizing (A i)
        (Set.range (fun q : σ i => (A i).evalFrom q (((List.ofFn ws).take i.val).flatten))) w } := by
      exact Set.mem_image_of_mem _ h_sub
    have h_inf_le : dfa_subset_reset_threshold (A i)
      (Set.range (fun q : σ i => (A i).evalFrom q (((List.ofFn ws).take i.val).flatten))) ≤
      (w_opt.length : WithTop ℕ) := by
      unfold dfa_subset_reset_threshold
      exact sInf_le h_mem
    have h_top : ((ws i).length : WithTop ℕ) ≤ (w_opt.length : WithTop ℕ) := by
      rw [h_len_eq]
      exact h_inf_le
    exact WithTop.coe_le_coe.mp h_top
  calc (∑ i : Fin k, (ws i).length)
    _ ≤ ∑ i : Fin k, w_opt.length := Finset.sum_le_sum (fun i _ => h_le i)
    _ = k * w_opt.length := by simp
