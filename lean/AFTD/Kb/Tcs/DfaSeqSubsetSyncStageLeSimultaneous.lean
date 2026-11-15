import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSimultaneouslySynchronizing
import AFTD.Kb.Tcs.DfaIsSeqSubsetSyncChoice
import AFTD.Kb.Tcs.DfaIsSubsetSynchronizing
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.DfaSubsetResetThreshold

/-!
# dfa_seq_subset_sync_stage_le_simultaneous

Topic: automata   Node: c8bb93c65bb6

Provenance: formalization of a published result. Source: arXiv:2611.09136

For any family of k deterministic finite automata A, any sequential subset synchronization choice ws, and any simultaneously synchronizing word w_opt, the length of each chosen word ws i is at most the length of w_opt.
-/

/-- At each stage i of sequential subset synchronization, the chosen shortest word has length at most that of any simultaneously synchronizing word. -/
theorem dfa_seq_subset_sync_stage_le_simultaneous {α : Type*} {k : ℕ} {σ : Fin k → Type*}
    (A : (i : Fin k) → DFA α (σ i)) (ws : Fin k → List α)
    (h_choice : dfa_is_seq_subset_sync_choice A ws)
    (w_opt : List α) (h_opt : dfa_is_simultaneously_synchronizing A w_opt)
    (i : Fin k) :
    (ws i).length ≤ w_opt.length := by
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
