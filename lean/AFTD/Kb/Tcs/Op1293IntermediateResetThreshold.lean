import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizable
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaProdResetThresholdBounds
import AFTD.Kb.Tcs.Op1293ProductResetThresholdUpperBoundAttained
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.Op1293ProductResetThresholdLowerBoundAttained

/-!
# op_1293_intermediate_reset_threshold

Topic: automata   Node: 55db667eb9c8

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 7, open question 2

Open Problem OP-1293 (arXiv:2611.09136 Sec. 7, open question 2): For every finite alphabet α with at least two symbols, any positive integers k₁ and k₂, and any integer k satisfying max k₁ k₂ ≤ k ≤ k₁ + k₂, there exist finite state types σ₁, σ₂ and synchronizable DFAs A₁ : DFA α σ₁ and A₂ : DFA α σ₂ with reset thresholds dfa_reset_threshold A₁ = k₁ and dfa_reset_threshold A₂ = k₂ such that the direct product dfa_prod A₁ A₂ has reset threshold dfa_reset_threshold (dfa_prod A₁ A₂) = k.
-/

def op_1293_intermediate_reset_threshold_step {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂) :
    Fin (k₂ + 1) → α → Fin (k₂ + 1) := fun q x =>
  if x = b then
    ⟨min (q.val + 1) k₂, Nat.lt_succ_of_le (min_le_right _ _)⟩
  else if h : x = a ∧ q.val < m then
    ⟨q.val + 1, by omega⟩
  else
    q

def op_1293_intermediate_reset_threshold_DFA {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂) :
    DFA α (Fin (k₂ + 1)) :=
  { step := op_1293_intermediate_reset_threshold_step k₂ m a b hm, start := 0, accept := ∅ }

theorem op_1293_intermediate_reset_threshold_step_b {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂) (q : Fin (k₂ + 1)) :
    op_1293_intermediate_reset_threshold_step k₂ m a b hm q b =
    op_1293_product_reset_threshold_upper_bound_attained_letterChainStep k₂ b q b := by
  dsimp [op_1293_intermediate_reset_threshold_step, op_1293_product_reset_threshold_upper_bound_attained_letterChainStep]
  simp

theorem op_1293_intermediate_reset_threshold_evalFrom_replicate_b {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂)
    (n : ℕ) (q : Fin (k₂ + 1)) :
    (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom q (List.replicate n b) =
    (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₂ b).evalFrom q (List.replicate n b) := by
  induction n generalizing q with
  | zero => simp [DFA.evalFrom]
  | succ n ih =>
    rw [List.replicate_succ, DFA.evalFrom_cons, DFA.evalFrom_cons]
    have : (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).step q b =
      (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₂ b).step q b :=
      op_1293_intermediate_reset_threshold_step_b k₂ m a b hm q
    rw [this, ih]

theorem op_1293_intermediate_reset_threshold_sync_replicate_b {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂) (hk₂ : 1 ≤ k₂) :
    dfa_is_synchronizing (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm) (List.replicate k₂ b) := by
  intro q₁ q₂
  rw [op_1293_intermediate_reset_threshold_evalFrom_replicate_b, op_1293_intermediate_reset_threshold_evalFrom_replicate_b]
  have hsync := (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₂ b (List.replicate k₂ b)).mpr (by simp)
  exact hsync q₁ q₂

theorem op_1293_intermediate_reset_threshold_step_top {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂) (x : α) :
    op_1293_intermediate_reset_threshold_step k₂ m a b hm ⟨k₂, Nat.lt_succ_self k₂⟩ x = ⟨k₂, Nat.lt_succ_self k₂⟩ := by
  dsimp [op_1293_intermediate_reset_threshold_step]
  split_ifs with h1 h2
  · ext; simp
  · exfalso; omega
  · rfl

theorem op_1293_intermediate_reset_threshold_evalFrom_top {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂)
    (w : List α) :
    (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom ⟨k₂, Nat.lt_succ_self k₂⟩ w = ⟨k₂, Nat.lt_succ_self k₂⟩ := by
  induction w with
  | nil => simp [DFA.evalFrom]
  | cons x w ih =>
    rw [DFA.evalFrom_cons]
    have : (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).step ⟨k₂, Nat.lt_succ_self k₂⟩ x = ⟨k₂, Nat.lt_succ_self k₂⟩ :=
      op_1293_intermediate_reset_threshold_step_top k₂ m a b hm x
    rw [this, ih]

theorem op_1293_intermediate_reset_threshold_step_val_le_succ {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂)
    (q : Fin (k₂ + 1)) (x : α) :
    (op_1293_intermediate_reset_threshold_step k₂ m a b hm q x).val ≤ q.val + 1 := by
  dsimp [op_1293_intermediate_reset_threshold_step]
  split_ifs with h1 h2
  · exact le_trans (min_le_left _ _) le_rfl
  · exact le_rfl
  · omega

theorem op_1293_intermediate_reset_threshold_evalFrom_zero_le_length {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂)
    (w : List α) :
    ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w).val ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [DFA.evalFrom]
  | append_singleton w x ih =>
    rw [show (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 (w ++ [x]) =
      op_1293_intermediate_reset_threshold_step k₂ m a b hm ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w) x by
      simp [DFA.evalFrom, op_1293_intermediate_reset_threshold_DFA]]
    have hstep := op_1293_intermediate_reset_threshold_step_val_le_succ k₂ m a b hm ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w) x
    rw [List.length_append, List.length_singleton]
    omega

theorem op_1293_intermediate_reset_threshold_sync_len_le {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂)
    (w : List α) (hw : dfa_is_synchronizing (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm) w) :
    k₂ ≤ w.length := by
  have htop := hw 0 ⟨k₂, Nat.lt_succ_self k₂⟩
  rw [op_1293_intermediate_reset_threshold_evalFrom_top] at htop
  have hval : ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w).val = k₂ := by
    rw [htop]
  have hlen := op_1293_intermediate_reset_threshold_evalFrom_zero_le_length k₂ m a b hm w
  omega

theorem op_1293_intermediate_reset_threshold_A₂_reset_threshold {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂) (hk₂ : 1 ≤ k₂) :
    dfa_reset_threshold (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm) = ↑k₂ := by
  apply le_antisymm
  · have hsync := op_1293_intermediate_reset_threshold_sync_replicate_b k₂ m a b hm hk₂
    have hmem : (↑(List.replicate k₂ b).length : WithTop ℕ) ∈ (fun w => (↑w.length : WithTop ℕ)) '' {w | dfa_is_synchronizing (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm) w} := by
      exact ⟨List.replicate k₂ b, hsync, rfl⟩
    have hinf := sInf_le hmem
    rw [List.length_replicate] at hinf
    exact hinf
  · apply le_sInf
    rintro b_1 ⟨w, hw, rfl⟩
    exact WithTop.coe_le_coe.mpr (op_1293_intermediate_reset_threshold_sync_len_le k₂ m a b hm w hw)

theorem op_1293_intermediate_reset_threshold_evalFrom_zero_le_m_add_count_b {α : Type*} [DecidableEq α] (k₂ m : ℕ) (a b : α) (hm : m ≤ k₂)
    (w : List α) :
    ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w).val ≤ m + List.count b w := by
  induction w using List.reverseRecOn with
  | nil => simp [DFA.evalFrom]
  | append_singleton w x ih =>
    rw [show (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 (w ++ [x]) =
      op_1293_intermediate_reset_threshold_step k₂ m a b hm ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w) x by
      simp [DFA.evalFrom, op_1293_intermediate_reset_threshold_DFA]]
    rw [List.count_append]
    by_cases hx : x = b
    · rw [hx, List.count_singleton_self]
      dsimp [op_1293_intermediate_reset_threshold_step]
      simp only [↓reduceIte]
      have : min (((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w).val + 1) k₂ ≤
        ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w).val + 1 := min_le_left _ _
      change min (((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w).val + 1) k₂ ≤ m + (List.count b w + 1)
      omega
    · have hxb : List.count b [x] = 0 := by
        have : (x == b) = false := beq_false_of_ne hx
        simp [List.count, this]
      rw [hxb]
      dsimp [op_1293_intermediate_reset_threshold_step]
      simp only [if_neg hx]
      split_ifs with h1
      · change ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w).val + 1 ≤ m + (List.count b w + 0)
        omega
      · omega

theorem op_1293_intermediate_reset_threshold_evalFrom_replicate_a_val {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (k₂ m : ℕ) (hm : m ≤ k₂) (q : Fin (k₂ + 1)) (n : ℕ) :
    ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom q (List.replicate n a)).val = min (q.val + n) (max q.val m) := by
  induction n generalizing q with
  | zero => simp [DFA.evalFrom]
  | succ n ih =>
    rw [List.replicate_succ, DFA.evalFrom_cons]
    show ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom (op_1293_intermediate_reset_threshold_step k₂ m a b hm q a) (List.replicate n a)).val = _
    dsimp [op_1293_intermediate_reset_threshold_step]
    rw [if_neg hab]
    split_ifs with h
    · rw [ih]
      dsimp
      omega
    · rw [ih]
      have : m ≤ q.val := not_lt.mp (fun hlt => h ⟨rfl, hlt⟩)
      omega

theorem op_1293_intermediate_reset_threshold_evalFrom_word_eq_top {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (k₁ k₂ m : ℕ) (hm : m ≤ k₂) (hmk₁ : m ≤ k₁) (q : Fin (k₂ + 1)) :
    (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom q (List.replicate k₁ a ++ List.replicate (k₂ - m) b) =
    ⟨k₂, Nat.lt_succ_self k₂⟩ := by
  simp only [DFA.evalFrom, List.foldl_append]
  have h_mid := op_1293_intermediate_reset_threshold_evalFrom_replicate_a_val hab k₂ m hm q k₁
  set q' := (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom q (List.replicate k₁ a)
  have hq' : m ≤ q'.val := by
    change m ≤ ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom q (List.replicate k₁ a)).val
    rw [h_mid]
    omega
  have h_b := op_1293_intermediate_reset_threshold_evalFrom_replicate_b k₂ m a b hm (k₂ - m) q'
  change (op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom q' (List.replicate (k₂ - m) b) = ⟨k₂, Nat.lt_succ_self k₂⟩
  rw [h_b]
  ext
  rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_evalFrom_val]
  rw [List.count_replicate_self]
  dsimp
  omega

/-- Open Problem OP-1293: Every intermediate value between max(rt(A₁), rt(A₂)) and rt(A₁) + rt(A₂) is attainable as the reset threshold of the direct product of two synchronizable DFAs over an alphabet of size at least 2. -/
theorem op_1293_intermediate_reset_threshold (α : Type*) [Fintype α] (hα : 2 ≤ Fintype.card α) (k₁ k₂ k : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (h_lower : max k₁ k₂ ≤ k) (h_upper : k ≤ k₁ + k₂) : ∃ (σ₁ σ₂ : Type) (_ : Fintype σ₁) (_ : Fintype σ₂) (A₁ : DFA α σ₁) (A₂ : DFA α σ₂), dfa_is_synchronizable A₁ ∧ dfa_is_synchronizable A₂ ∧ dfa_reset_threshold A₁ = ↑k₁ ∧ dfa_reset_threshold A₂ = ↑k₂ ∧ dfa_reset_threshold (dfa_prod A₁ A₂) = ↑k := by
  classical
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hnt : Nonempty (Fin (k₁ + 1)) := ⟨0⟩
  have hnt2 : Nonempty (Fin (k₂ + 1)) := ⟨0⟩
  set m := k₁ + k₂ - k
  have hm : m ≤ k₂ := by omega
  have hmk₁ : m ≤ k₁ := by omega
  set A₁ := op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA k₁ a
  set A₂ := op_1293_intermediate_reset_threshold_DFA k₂ m a b hm
  set w₀ := List.replicate k₁ a ++ List.replicate (k₂ - m) b
  refine ⟨Fin (k₁ + 1), Fin (k₂ + 1), inferInstance, inferInstance, A₁, A₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨List.replicate k₁ a, (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₁ a _).mpr (by simp)⟩
  · exact ⟨List.replicate k₂ b, op_1293_intermediate_reset_threshold_sync_replicate_b k₂ m a b hm hk₂⟩
  · exact op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_reset_threshold k₁ hk₁ a
  · exact op_1293_intermediate_reset_threshold_A₂_reset_threshold k₂ m a b hm hk₂
  · apply le_antisymm
    · have hcounts := op_1293_product_reset_threshold_upper_bound_attained_count_replicate_append_replicate hab k₁ (k₂ - m)
      have hw₀_sync1 : dfa_is_synchronizing A₁ w₀ := by
        rw [op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₁ a w₀]
        exact le_of_eq hcounts.left.symm
      have hw₀_sync2 : dfa_is_synchronizing A₂ w₀ := by
        intro q₁ q₂
        rw [op_1293_intermediate_reset_threshold_evalFrom_word_eq_top hab k₁ k₂ m hm hmk₁ q₁]
        rw [op_1293_intermediate_reset_threshold_evalFrom_word_eq_top hab k₁ k₂ m hm hmk₁ q₂]
      have hw₀_sync : dfa_is_synchronizing (dfa_prod A₁ A₂) w₀ := by
        rw [op_1293_dfa_prod_is_synchronizing_iff]
        exact ⟨hw₀_sync1, hw₀_sync2⟩
      have hw₀_len : w₀.length = k := by
        change (List.replicate k₁ a ++ List.replicate (k₂ - m) b).length = k
        rw [hcounts.right.right]
        omega
      have hmem : (↑w₀.length : WithTop ℕ) ∈ (fun w => (↑w.length : WithTop ℕ)) '' {w | dfa_is_synchronizing (dfa_prod A₁ A₂) w} :=
        ⟨w₀, hw₀_sync, rfl⟩
      have hinf := sInf_le hmem
      rw [hw₀_len] at hinf
      exact hinf
    · apply le_sInf
      rintro b_1 ⟨w, hw, rfl⟩
      change dfa_is_synchronizing (dfa_prod A₁ A₂) w at hw
      rw [op_1293_dfa_prod_is_synchronizing_iff] at hw
      have hw1 := (op_1293_product_reset_threshold_upper_bound_attained_letterChainDFA_is_synchronizing_iff hk₁ a w).mp hw.left
      have hw2_sync := hw.right
      have htop := hw2_sync 0 ⟨k₂, Nat.lt_succ_self k₂⟩
      rw [op_1293_intermediate_reset_threshold_evalFrom_top] at htop
      have hval : ((op_1293_intermediate_reset_threshold_DFA k₂ m a b hm).evalFrom 0 w).val = k₂ := by
        rw [htop]
      have hle_m := op_1293_intermediate_reset_threshold_evalFrom_zero_le_m_add_count_b k₂ m a b hm w
      rw [hval] at hle_m
      have htotal := op_1293_product_reset_threshold_upper_bound_attained_count_add_count_le_length hab w
      have hlen : k ≤ w.length := by omega
      exact WithTop.coe_le_coe.mpr hlen
