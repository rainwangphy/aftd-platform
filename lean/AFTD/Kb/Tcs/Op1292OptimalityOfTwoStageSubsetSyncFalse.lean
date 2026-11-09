import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaIsSynchronizable
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaSubsetResetThreshold
import AFTD.Kb.Tcs.DfaIsSubsetSynchronizing

/-!
# op_1292_optimality_of_two_stage_subset_sync_false

Topic: automata   Node: 8cd53e2726fe

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 7, open question 4

Open Problem OP-1292 does not hold: it is not the case that for every pair of synchronizable DFAs `A₁` and `A₂` over a shared finite alphabet, there exists a shortest synchronizing word `w₁` of `A₁` such that the reset threshold of `dfa_prod A₁ A₂` equals the length of `w₁` plus the subset reset threshold of `Set.range (fun q => A₂.evalFrom q w₁)` in `A₂`.
-/

def op_1292_A1_step : Fin 2 → Fin 2 → Fin 2
  | _, 0 => 0
  | 0, 1 => 0
  | 1, 1 => 1

def op_1292_A2_step : Fin 3 → Fin 2 → Fin 3
  | 0, 0 => 0
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 2, 0 => 2
  | 2, 1 => 1

def op_1292_A1 : DFA (Fin 2) (Fin 2) := ⟨op_1292_A1_step, 0, ∅⟩
def op_1292_A2 : DFA (Fin 2) (Fin 3) := ⟨op_1292_A2_step, 0, ∅⟩

lemma op_1292_A1_sync : dfa_is_synchronizable op_1292_A1 :=
  ⟨[0], by dsimp [dfa_is_synchronizing, DFA.evalFrom, op_1292_A1, op_1292_A1_step]; decide⟩

lemma op_1292_A2_sync : dfa_is_synchronizable op_1292_A2 :=
  ⟨[1, 0], by dsimp [dfa_is_synchronizing, DFA.evalFrom, op_1292_A2, op_1292_A2_step]; decide⟩

lemma op_1292_prod_rt_le_two : dfa_reset_threshold (dfa_prod op_1292_A1 op_1292_A2) ≤ 2 := by
  dsimp [dfa_reset_threshold]
  apply sInf_le
  refine ⟨[1, 0], ?_, ?_⟩
  · dsimp [dfa_is_synchronizing, DFA.evalFrom, dfa_prod, op_1292_A1, op_1292_A2, op_1292_A1_step, op_1292_A2_step]
    decide
  · rfl

lemma op_1292_A1_rt_eq_one : dfa_reset_threshold op_1292_A1 = 1 := by
  apply le_antisymm
  · dsimp [dfa_reset_threshold]
    apply sInf_le
    refine ⟨[0], ?_, ?_⟩
    · dsimp [dfa_is_synchronizing, DFA.evalFrom, op_1292_A1, op_1292_A1_step]
      decide
    · rfl
  · dsimp [dfa_reset_threshold]
    apply le_sInf
    rintro b ⟨w, hw, rfl⟩
    cases w with
    | nil =>
      exfalso
      have hneq : (op_1292_A1.evalFrom 0 [] : Fin 2) ≠ op_1292_A1.evalFrom 1 [] := by decide
      exact hneq (hw 0 1)
    | cons x xs =>
      simp only [List.length_cons]
      norm_cast
      omega

lemma op_1292_w1_eq_zero (w₁ : List (Fin 2)) (hw₁ : dfa_is_synchronizing op_1292_A1 w₁) (hlen : w₁.length = 1) :
    w₁ = [0] := by
  match w₁ with
  | [x] =>
    fin_cases x
    · rfl
    · exfalso
      have hneq : (op_1292_A1.evalFrom 0 [1] : Fin 2) ≠ op_1292_A1.evalFrom 1 [1] := by decide
      exact hneq (hw₁ 0 1)

lemma op_1292_subset_rt_ge_two :
    2 ≤ dfa_subset_reset_threshold op_1292_A2 (Set.range (fun q => op_1292_A2.evalFrom q [0])) := by
  dsimp [dfa_subset_reset_threshold]
  apply le_sInf
  rintro b ⟨v, hv, rfl⟩
  have h0 : (0 : Fin 3) ∈ Set.range (fun q => op_1292_A2.evalFrom q [0]) := ⟨0, rfl⟩
  have h2 : (2 : Fin 3) ∈ Set.range (fun q => op_1292_A2.evalFrom q [0]) := ⟨2, rfl⟩
  have hsync := hv 0 h0 2 h2
  match v with
  | [] =>
    exfalso
    revert hsync
    decide
  | [x] =>
    fin_cases x
    · exfalso; revert hsync; decide
    · exfalso; revert hsync; decide
  | _ :: _ :: tl =>
    simp only [List.length_cons]
    norm_cast
    omega

/-- Refutation of OP-1292: two-stage subset synchronization using a shortest synchronizing word of A₁ is not always optimal for the direct product. -/
theorem op_1292_optimality_of_two_stage_subset_sync_false : ¬ (∀ (α : Type) [Fintype α] (σ₁ σ₂ : Type) [Fintype σ₁] [Fintype σ₂] (A₁ : DFA α σ₁) (A₂ : DFA α σ₂), dfa_is_synchronizable A₁ → dfa_is_synchronizable A₂ → ∃ w₁ : List α, dfa_is_synchronizing A₁ w₁ ∧ (w₁.length : WithTop ℕ) = dfa_reset_threshold A₁ ∧ dfa_reset_threshold (dfa_prod A₁ A₂) = (w₁.length : WithTop ℕ) + dfa_subset_reset_threshold A₂ (Set.range (fun q => A₂.evalFrom q w₁))) := by
  intro h
  obtain ⟨w₁, hw₁_sync, hw₁_len, heq⟩ :=
    h (Fin 2) (Fin 2) (Fin 3) op_1292_A1 op_1292_A2 op_1292_A1_sync op_1292_A2_sync
  rw [op_1292_A1_rt_eq_one] at hw₁_len
  have hlen : w₁.length = 1 := by
    exact_mod_cast hw₁_len
  have hw₁ : w₁ = [0] := op_1292_w1_eq_zero w₁ hw₁_sync hlen
  subst hw₁
  rw [hw₁_len] at heq
  have h_prod_le : dfa_reset_threshold (dfa_prod op_1292_A1 op_1292_A2) ≤ 2 := op_1292_prod_rt_le_two
  rw [heq] at h_prod_le
  have h_sub_ge := op_1292_subset_rt_ge_two
  have h1 : (3 : WithTop ℕ) ≤ 1 + dfa_subset_reset_threshold op_1292_A2 (Set.range fun q => op_1292_A2.evalFrom q [0]) := by
    have : (3 : WithTop ℕ) = 1 + 2 := rfl
    rw [this]
    exact add_le_add_right h_sub_ge 1
  have : (3 : WithTop ℕ) ≤ 2 := h1.trans h_prod_le
  revert this
  decide
