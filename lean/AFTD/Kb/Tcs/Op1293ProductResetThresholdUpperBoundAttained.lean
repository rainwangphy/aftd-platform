import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizable
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.Op1293ProductResetThresholdLowerBoundAttained

/-!
# op_1293_product_reset_threshold_upper_bound_attained

Topic: automata   Node: d76ca7972d12

Provenance: formalization of a published result. Source: arXiv:2611.09136 Example 3.7, Proposition 3.4

For every finite alphabet α with at least two symbols and positive integers k₁, k₂, there exist finite state types σ₁, σ₂ and synchronizable DFAs A₁ : DFA α σ₁ and A₂ : DFA α σ₂ with dfa_reset_threshold A₁ = k₁ and dfa_reset_threshold A₂ = k₂ such that the reset threshold of their direct product attains the upper bound k₁ + k₂.
-/

open List

def op_1293_product_reset_threshold_upper_bound_attained_letterChainStep
    {α : Type*} [DecidableEq α] (k : ℕ) (a : α) (q : Fin (k + 1)) (x : α) : Fin (k + 1) :=
  if x = a then ⟨min (q.val + 1) k, by omega⟩ else q

def op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA
    {α : Type*} [DecidableEq α] (k : ℕ) (a : α) : DFA α (Fin (k + 1)) where
  step := op_1293_product_reset_threshold_upper_bound_attained_letterChainStep k a
  start := 0
  accept := ∅

theorem op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_evalFrom_val
    {α : Type*} [DecidableEq α] (k : ℕ) (a : α) (q : Fin (k + 1)) (w : List α) :
    ((op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k a).evalFrom q w).val =
      min (q.val + w.count a) k := by
  induction w generalizing q with
  | nil =>
    rw [DFA.evalFrom_nil]
    simp only [List.count_nil, add_zero]
    have := q.is_lt
    omega
  | cons x xs ih =>
    rw [DFA.evalFrom_cons]
    change ((op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k a).evalFrom
      (op_1293_product_reset_threshold_upper_bound_attained_letterChainStep k a q x) xs).val = _
    rw [ih]
    dsimp [op_1293_product_reset_threshold_upper_bound_attained_letterChainStep]
    split_ifs with hx
    · simp [hx]
      omega
    · simp [hx]

theorem op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff
    {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) (a : α) (w : List α) :
    dfa_is_synchronizing (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k a) w ↔
      k ≤ w.count a := by
  constructor
  · intro h
    have hq := h ⟨0, by omega⟩ ⟨k, by omega⟩
    have h1 := op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_evalFrom_val k a ⟨0, by omega⟩ w
    have h2 := op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_evalFrom_val k a ⟨k, by omega⟩ w
    have heq : ((op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k a).evalFrom ⟨0, by omega⟩ w).val =
               ((op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k a).evalFrom ⟨k, by omega⟩ w).val := by rw [hq]
    rw [h1, h2] at heq
    dsimp at heq
    omega
  · intro h q₁ q₂
    ext
    rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_evalFrom_val,
        op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_evalFrom_val]
    omega

theorem op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_reset_threshold
    {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (a : α) :
    dfa_reset_threshold (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k a) = ↑k := by
  apply le_antisymm
  · have hw : dfa_is_synchronizing (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k a) (List.replicate k a) := by
      rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk]
      simp
    have hmem : (k : WithTop ℕ) ∈ (fun w => (w.length : WithTop ℕ)) ''
        {w | dfa_is_synchronizing (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k a) w} := by
      exact ⟨List.replicate k a, hw, by simp⟩
    exact sInf_le hmem
  · apply le_sInf
    rintro b ⟨w, hw, rfl⟩
    dsimp at hw
    rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk] at hw
    have hlen : k ≤ w.length := hw.trans List.count_le_length
    exact WithTop.coe_le_coe.mpr hlen

theorem op_1293_product_reset_threshold_upper_bound_attained_count_add_count_le_length
    {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) (w : List α) :
    w.count a + w.count b ≤ w.length := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, List.length_cons]
    split_ifs with h1 h2
    · rw [beq_iff_eq] at h1 h2
      subst h1 h2; contradiction
    · omega
    · omega
    · omega

theorem op_1293_product_reset_threshold_upper_bound_attained_count_replicate_append_replicate
    {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) (k₁ k₂ : ℕ) :
    (List.replicate k₁ a ++ List.replicate k₂ b).count a = k₁ ∧
    (List.replicate k₁ a ++ List.replicate k₂ b).count b = k₂ ∧
    (List.replicate k₁ a ++ List.replicate k₂ b).length = k₁ + k₂ := by
  have h_ne1 : (b == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm hab)
  have h_ne2 : (a == b) = false := beq_eq_false_iff_ne.mpr hab
  simp [List.count_append, List.count_replicate, h_ne1, h_ne2]

theorem op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_prod_reset_threshold
    {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (k₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    dfa_reset_threshold (dfa_prod (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₁ a)
                                  (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₂ b)) = ↑(k₁ + k₂) := by
  have : Nonempty (Fin (k₁ + 1)) := ⟨0⟩
  have : Nonempty (Fin (k₂ + 1)) := ⟨0⟩
  apply le_antisymm
  · have hsync : dfa_is_synchronizing (dfa_prod (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₁ a)
                                                (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₂ b))
        (List.replicate k₁ a ++ List.replicate k₂ b) := by
      rw [op_1293_dfa_prod_is_synchronizing_iff]
      rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₁]
      rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₂]
      have hcounts := op_1293_product_reset_threshold_upper_bound_attained_count_replicate_append_replicate hab k₁ k₂
      exact ⟨le_of_eq hcounts.1.symm, le_of_eq hcounts.2.1.symm⟩
    have hlen : (List.replicate k₁ a ++ List.replicate k₂ b).length = k₁ + k₂ :=
      (op_1293_product_reset_threshold_upper_bound_attained_count_replicate_append_replicate hab k₁ k₂).2.2
    have hmem : ((k₁ + k₂ : ℕ) : WithTop ℕ) ∈
        (fun w => (w.length : WithTop ℕ)) ''
          {w | dfa_is_synchronizing (dfa_prod (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₁ a)
                                              (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₂ b)) w} := by
      refine ⟨List.replicate k₁ a ++ List.replicate k₂ b, hsync, ?_⟩
      dsimp
      rw [hlen]
    exact sInf_le hmem
  · apply le_sInf
    rintro b ⟨w, hw, rfl⟩
    dsimp at hw
    rw [op_1293_dfa_prod_is_synchronizing_iff] at hw
    rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₁] at hw
    rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₂] at hw
    have hsum : k₁ + k₂ ≤ w.count a + w.count b := add_le_add hw.1 hw.2
    have htotal := hsum.trans (op_1293_product_reset_threshold_upper_bound_attained_count_add_count_le_length hab w)
    exact WithTop.coe_le_coe.mpr htotal

/-- The upper bound rt(A₁) + rt(A₂) for the product reset threshold is attained. -/
theorem op_1293_product_reset_threshold_upper_bound_attained (α : Type*) [Fintype α] (hα : 2 ≤ Fintype.card α) (k₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) : ∃ (σ₁ σ₂ : Type) (_ : Fintype σ₁) (_ : Fintype σ₂) (A₁ : DFA α σ₁) (A₂ : DFA α σ₂), dfa_is_synchronizable A₁ ∧ dfa_is_synchronizable A₂ ∧ dfa_reset_threshold A₁ = ↑k₁ ∧ dfa_reset_threshold A₂ = ↑k₂ ∧ dfa_reset_threshold (dfa_prod A₁ A₂) = ↑(k₁ + k₂) := by
  classical
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine ⟨Fin (k₁ + 1), Fin (k₂ + 1), inferInstance, inferInstance,
          op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₁ a,
          op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₂ b, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨List.replicate k₁ a, (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₁ a _).mpr (by simp)⟩
  · exact ⟨List.replicate k₂ b, (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₂ b _).mpr (by simp)⟩
  · exact op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_reset_threshold k₁ hk₁ a
  · exact op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_reset_threshold k₂ hk₂ b
  · exact op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_prod_reset_threshold hab k₁ k₂ hk₁ hk₂
