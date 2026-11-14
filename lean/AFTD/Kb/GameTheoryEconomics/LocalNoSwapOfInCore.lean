import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsInCore
import AFTD.Kb.GameTheoryEconomics.MarginalVector
import AFTD.Kb.GameTheoryEconomics.LocalNoSwap
import AFTD.Kb.GameTheoryEconomics.OrderPrefix
import AFTD.Kb.GameTheoryEconomics.Predecessors
import AFTD.Kb.GameTheoryEconomics.OrderPrefixZero

/-!
# local_no_swap_of_in_core

Topic: general_equilibrium   Node: 24bfea31171d

Provenance: helper lemma. arXiv:2611.16207, Lemma 2

For any cooperative game v on a finite type α satisfying v(∅) = 0 and any ordering bijection e : Fin (Fintype.card α) ≃ α, if the marginal worth vector marginal_vector v e belongs to the core of v (is_in_core v (marginal_vector v e)), then the local no-swap condition local_no_swap v e holds.
-/

open Finset

private theorem local_no_swap_of_in_core_mem_order_prefix_iff {α : Type*} [DecidableEq α] [Fintype α]
    (e : Fin (Fintype.card α) ≃ α) (k : ℕ) (x : α) :
    x ∈ order_prefix e k ↔ (e.symm x : ℕ) < k := by
  dsimp [order_prefix]
  rw [mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_filter] at ha
    rw [Equiv.symm_apply_apply]
    exact ha.2
  · intro h
    refine ⟨e.symm x, ?_, Equiv.apply_symm_apply e x⟩
    rw [mem_filter]
    exact ⟨mem_univ _, h⟩

private theorem local_no_swap_of_in_core_order_prefix_succ {α : Type*} [DecidableEq α] [Fintype α]
    (e : Fin (Fintype.card α) ≃ α) (k : ℕ) (hk : k < Fintype.card α) :
    order_prefix e (k + 1) = insert (e ⟨k, hk⟩) (order_prefix e k) := by
  ext x
  rw [local_no_swap_of_in_core_mem_order_prefix_iff, mem_insert, local_no_swap_of_in_core_mem_order_prefix_iff]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · right; exact hlt
    · left
      have : e.symm x = ⟨k, hk⟩ := Fin.ext heq
      rw [← this, Equiv.apply_symm_apply]
  · rintro (rfl | hlt)
    · rw [Equiv.symm_apply_apply]
      exact Nat.lt_succ_self k
    · exact Nat.lt_succ_of_lt hlt

private theorem local_no_swap_of_in_core_not_mem_order_prefix_of_ge {α : Type*} [DecidableEq α] [Fintype α]
    (e : Fin (Fintype.card α) ≃ α) {k m : ℕ} (hm : m < Fintype.card α) (hkm : k ≤ m) :
    e ⟨m, hm⟩ ∉ order_prefix e k := by
  rw [local_no_swap_of_in_core_mem_order_prefix_iff, Equiv.symm_apply_apply]
  exact not_lt_of_ge hkm

private theorem local_no_swap_of_in_core_predecessors_apply {α : Type*} [DecidableEq α] [Fintype α]
    (e : Fin (Fintype.card α) ≃ α) (m : Fin (Fintype.card α)) :
    predecessors e (e m) = order_prefix e m.val := by
  dsimp [predecessors, order_prefix]
  rw [Equiv.symm_apply_apply]
  rfl

private theorem local_no_swap_of_in_core_sum_marginal_vector_order_prefix {α : Type*} [DecidableEq α] [Fintype α]
    (v : Finset α → ℝ) (e : Fin (Fintype.card α) ≃ α) :
    ∀ (k : ℕ), k ≤ Fintype.card α →
      ∑ i ∈ order_prefix e k, marginal_vector v e i = v (order_prefix e k) - v ∅ := by
  intro k
  induction' k with k ih
  · intro _
    rw [order_prefix_zero]
    simp
  · intro hk
    have hk_lt : k < Fintype.card α := Nat.lt_of_succ_le hk
    have hk_le : k ≤ Fintype.card α := Nat.le_of_lt hk_lt
    rw [local_no_swap_of_in_core_order_prefix_succ e k hk_lt]
    rw [sum_insert (local_no_swap_of_in_core_not_mem_order_prefix_of_ge e hk_lt le_rfl)]
    rw [ih hk_le]
    dsimp [marginal_vector]
    rw [local_no_swap_of_in_core_predecessors_apply e ⟨k, hk_lt⟩]
    rw [← local_no_swap_of_in_core_order_prefix_succ e k hk_lt]
    ring

/-- If the marginal worth vector of an ordering is in the core, the local no-swap condition holds. -/
theorem local_no_swap_of_in_core {α : Type*} [DecidableEq α] [Fintype α]
    (v : Finset α → ℝ) (hv0 : v ∅ = 0) (e : Fin (Fintype.card α) ≃ α)
    (h_core : is_in_core v (marginal_vector v e)) :
    local_no_swap v e := by
  intro k hk
  have hk1 : k + 1 < Fintype.card α := by omega
  have hk_le : k ≤ Fintype.card α := by omega
  have hk_not_mem : e ⟨k + 1, hk1⟩ ∉ order_prefix e k :=
    local_no_swap_of_in_core_not_mem_order_prefix_of_ge e hk1 (by omega)
  let S := insert (e ⟨k + 1, hk1⟩) (order_prefix e k)
  have hS_le : v S ≤ ∑ i ∈ S, marginal_vector v e i := h_core.2 S
  have h_sum_S : ∑ i ∈ S, marginal_vector v e i =
      marginal_vector v e (e ⟨k + 1, hk1⟩) + ∑ i ∈ order_prefix e k, marginal_vector v e i :=
    Finset.sum_insert hk_not_mem
  have h_sum_k : ∑ i ∈ order_prefix e k, marginal_vector v e i = v (order_prefix e k) := by
    have := local_no_swap_of_in_core_sum_marginal_vector_order_prefix v e k hk_le
    rw [hv0, sub_zero] at this
    exact this
  have h_mv : marginal_vector v e (e ⟨k + 1, hk1⟩) =
      v (order_prefix e (k + 2)) - v (order_prefix e (k + 1)) := by
    dsimp [marginal_vector]
    rw [local_no_swap_of_in_core_predecessors_apply e ⟨k + 1, hk1⟩]
    have hk1_lt : k + 1 < Fintype.card α := by omega
    have hsucc := local_no_swap_of_in_core_order_prefix_succ e (k + 1) hk1_lt
    exact congrArg (fun s => v s - v (order_prefix e (k + 1))) hsucc.symm
  linarith
