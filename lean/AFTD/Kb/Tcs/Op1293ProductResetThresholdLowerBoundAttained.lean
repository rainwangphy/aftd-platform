import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizable
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# op_1293_product_reset_threshold_lower_bound_attained

Topic: automata   Node: b22a93cf0e98

Provenance: formalization of a published result. Source: arXiv:2611.09136 Example 3.6, Proposition 3.4

For every nonempty finite alphabet α and positive integers k₁, k₂, there exist finite state types σ₁, σ₂ and synchronizable DFAs A₁ : DFA α σ₁ and A₂ : DFA α σ₂ with dfa_reset_threshold A₁ = k₁ and dfa_reset_threshold A₂ = k₂ such that the reset threshold of their direct product attains the lower bound max k₁ k₂.
-/

def op_1293_chainDFA (α : Type*) (k : ℕ) : DFA α (Fin (k + 1)) where
  step q _ := ⟨min (q.val + 1) k, by
    apply Nat.lt_succ_of_le
    exact Nat.min_le_right _ _⟩
  start := 0
  accept := ∅

lemma op_1293_chainDFA_step_val (α : Type*) (k : ℕ) (q : Fin (k + 1)) (a : α) :
    ((op_1293_chainDFA α k).step q a).val = min (q.val + 1) k := rfl

lemma op_1293_chainDFA_evalFrom_val (α : Type*) (k : ℕ) (q : Fin (k + 1)) (w : List α) :
    ((op_1293_chainDFA α k).evalFrom q w).val = min (q.val + w.length) k := by
  induction' w using List.reverseRecOn with w a ih
  · simp only [DFA.evalFrom_nil, List.length_nil, add_zero]
    omega
  · rw [DFA.evalFrom_append_singleton, op_1293_chainDFA_step_val, ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma op_1293_chainDFA_is_synchronizing_iff (α : Type*) {k : ℕ} (hk : 1 ≤ k) (w : List α) :
    dfa_is_synchronizing (op_1293_chainDFA α k) w ↔ k ≤ w.length := by
  constructor
  · intro h
    have hq := h ⟨0, by omega⟩ ⟨k, by omega⟩
    apply_fun Fin.val at hq
    rw [op_1293_chainDFA_evalFrom_val, op_1293_chainDFA_evalFrom_val] at hq
    dsimp only at hq
    omega
  · intro h q₁ q₂
    apply Fin.ext
    rw [op_1293_chainDFA_evalFrom_val, op_1293_chainDFA_evalFrom_val]
    omega

lemma op_1293_chainDFA_reset_threshold (α : Type*) [Nonempty α] (k : ℕ) (hk : 1 ≤ k) :
    dfa_reset_threshold (op_1293_chainDFA α k) = ↑k := by
  unfold dfa_reset_threshold
  apply le_antisymm
  · obtain ⟨x⟩ := (inferInstance : Nonempty α)
    have hw : dfa_is_synchronizing (op_1293_chainDFA α k) (List.replicate k x) := by
      rw [op_1293_chainDFA_is_synchronizing_iff α hk]
      simp
    have hmem : (k : WithTop ℕ) ∈ (fun w : List α => (w.length : WithTop ℕ)) '' { w | dfa_is_synchronizing (op_1293_chainDFA α k) w } := by
      exact ⟨List.replicate k x, hw, by simp⟩
    exact sInf_le hmem
  · apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    have : dfa_is_synchronizing (op_1293_chainDFA α k) w := hw
    rw [op_1293_chainDFA_is_synchronizing_iff α hk] at this
    exact WithTop.coe_le_coe.mpr this

lemma op_1293_dfa_prod_evalFrom {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂)
    (q₁ : σ₁) (q₂ : σ₂) (w : List α) :
    (dfa_prod A₁ A₂).evalFrom (q₁, q₂) w = (A₁.evalFrom q₁ w, A₂.evalFrom q₂ w) := by
  induction' w using List.reverseRecOn with w a ih
  · simp [DFA.evalFrom_nil]
  · rw [DFA.evalFrom_append_singleton, DFA.evalFrom_append_singleton, DFA.evalFrom_append_singleton, ih]
    rfl

lemma op_1293_dfa_prod_is_synchronizing_iff {α σ₁ σ₂ : Type*} [Nonempty σ₁] [Nonempty σ₂]
    (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) (w : List α) :
    dfa_is_synchronizing (dfa_prod A₁ A₂) w ↔ dfa_is_synchronizing A₁ w ∧ dfa_is_synchronizing A₂ w := by
  constructor
  · intro h
    obtain ⟨s₁⟩ := (inferInstance : Nonempty σ₁)
    obtain ⟨s₂⟩ := (inferInstance : Nonempty σ₂)
    constructor
    · intro q₁ q₂
      have := h (q₁, s₂) (q₂, s₂)
      rw [op_1293_dfa_prod_evalFrom, op_1293_dfa_prod_evalFrom] at this
      exact (Prod.ext_iff.mp this).1
    · intro q₁ q₂
      have := h (s₁, q₁) (s₁, q₂)
      rw [op_1293_dfa_prod_evalFrom, op_1293_dfa_prod_evalFrom] at this
      exact (Prod.ext_iff.mp this).2
  · rintro ⟨h₁, h₂⟩ ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    rw [op_1293_dfa_prod_evalFrom, op_1293_dfa_prod_evalFrom]
    exact Prod.ext (h₁ p₁ q₁) (h₂ p₂ q₂)

lemma op_1293_chainDFA_prod_reset_threshold (α : Type*) [Nonempty α] (k₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    dfa_reset_threshold (dfa_prod (op_1293_chainDFA α k₁) (op_1293_chainDFA α k₂)) = ↑(max k₁ k₂) := by
  have : Nonempty (Fin (k₁ + 1)) := ⟨0⟩
  have : Nonempty (Fin (k₂ + 1)) := ⟨0⟩
  unfold dfa_reset_threshold
  apply le_antisymm
  · obtain ⟨x⟩ := (inferInstance : Nonempty α)
    have hw : dfa_is_synchronizing (dfa_prod (op_1293_chainDFA α k₁) (op_1293_chainDFA α k₂)) (List.replicate (max k₁ k₂) x) := by
      rw [op_1293_dfa_prod_is_synchronizing_iff, op_1293_chainDFA_is_synchronizing_iff α hk₁, op_1293_chainDFA_is_synchronizing_iff α hk₂]
      simp
    have hmem : (↑(max k₁ k₂) : WithTop ℕ) ∈ (fun w : List α => (w.length : WithTop ℕ)) '' { w | dfa_is_synchronizing (dfa_prod (op_1293_chainDFA α k₁) (op_1293_chainDFA α k₂)) w } := by
      exact ⟨List.replicate (max k₁ k₂) x, hw, by simp⟩
    exact sInf_le hmem
  · apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    have : dfa_is_synchronizing (dfa_prod (op_1293_chainDFA α k₁) (op_1293_chainDFA α k₂)) w := hw
    rw [op_1293_dfa_prod_is_synchronizing_iff, op_1293_chainDFA_is_synchronizing_iff α hk₁, op_1293_chainDFA_is_synchronizing_iff α hk₂] at this
    have : max k₁ k₂ ≤ w.length := by omega
    exact WithTop.coe_le_coe.mpr this

/-- The lower bound max(rt(A₁), rt(A₂)) for the product reset threshold is attained. -/
theorem op_1293_product_reset_threshold_lower_bound_attained (α : Type*) [Fintype α] [Nonempty α] (k₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) : ∃ (σ₁ σ₂ : Type) (_ : Fintype σ₁) (_ : Fintype σ₂) (A₁ : DFA α σ₁) (A₂ : DFA α σ₂), dfa_is_synchronizable A₁ ∧ dfa_is_synchronizable A₂ ∧ dfa_reset_threshold A₁ = ↑k₁ ∧ dfa_reset_threshold A₂ = ↑k₂ ∧ dfa_reset_threshold (dfa_prod A₁ A₂) = ↑(max k₁ k₂) := by
  refine ⟨Fin (k₁ + 1), Fin (k₂ + 1), inferInstance, inferInstance, op_1293_chainDFA α k₁, op_1293_chainDFA α k₂, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty α)
    exact ⟨List.replicate k₁ x, (op_1293_chainDFA_is_synchronizing_iff α hk₁ _).mpr (by simp)⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty α)
    exact ⟨List.replicate k₂ x, (op_1293_chainDFA_is_synchronizing_iff α hk₂ _).mpr (by simp)⟩
  · exact op_1293_chainDFA_reset_threshold α k₁ hk₁
  · exact op_1293_chainDFA_reset_threshold α k₂ hk₂
  · exact op_1293_chainDFA_prod_reset_threshold α k₁ k₂ hk₁ hk₂
