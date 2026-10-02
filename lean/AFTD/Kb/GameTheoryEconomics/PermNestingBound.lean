import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PermCardLeftGtLe
import AFTD.Kb.GameTheoryEconomics.PermGapSum
import AFTD.Kb.GameTheoryEconomics.PermCrossInvSum

/-!
# perm_nesting_bound

Topic: matching_markets   Node: 2cd530c32624

For a permutation s of {0, ..., n-1} with k positions a such that s(a) < a: the number of pairs (a, b) with a < b and s(b) < s(a) and a, b on the same side (both s(x) < x or both not), plus the number of pairs with s(a) < a, s(b) >= b and not (b < a and s(a) < s(b)), plus k, is at most k(n - k).
-/

theorem perm_nesting_bound {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ a : Fin n, ∑ b : Fin n,
        if ((a : ℕ) < b ∧ (σ b : ℕ) < σ a ∧ ((σ a : ℕ) < a ↔ (σ b : ℕ) < b)) ∨
          ((σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ ¬((b : ℕ) < a ∧ (σ a : ℕ) < σ b)) then 1 else 0) +
      (∑ b : Fin n, if (σ b : ℕ) < b then 1 else 0) ≤
      (∑ b : Fin n, if (σ b : ℕ) < b then 1 else 0) *
        (n - ∑ b : Fin n, if (σ b : ℕ) < b then 1 else 0) := by
  set k := ∑ b : Fin n, if (σ b : ℕ) < b then 1 else 0 with hk
  -- the three pieces
  have hpt : ∀ a b : Fin n,
      (if ((a : ℕ) < b ∧ (σ b : ℕ) < σ a ∧ ((σ a : ℕ) < a ↔ (σ b : ℕ) < b)) ∨
          ((σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ ¬((b : ℕ) < a ∧ (σ a : ℕ) < σ b)) then 1 else 0 : ℕ) ≤
        (if (σ a : ℕ) < a ∧ (σ b : ℕ) < a ∧ (a : ℕ) < b then 1 else 0) +
        (if (a : ℕ) < b ∧ (σ b : ℕ) < σ a ∧ (a : ℕ) ≤ σ a ∧ (b : ℕ) ≤ σ b then 1 else 0) +
        (if (σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ ¬((b : ℕ) < a ∧ (σ a : ℕ) < σ b) then 1 else 0) := by
    intro a b
    by_cases h1 : (σ a : ℕ) < a <;> by_cases h2 : (σ b : ℕ) < b <;> split_ifs <;> omega
  have hS2 : (∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < b ∧ (σ b : ℕ) < σ a ∧ (a : ℕ) ≤ σ a ∧ (b : ℕ) ≤ σ b then 1 else 0) ≤
      ∑ a : Fin n, ∑ b : Fin n,
        if (a : ℕ) ≤ σ a ∧ (σ b : ℕ) < a ∧ (a : ℕ) < b then 1 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : (b : ℕ) ≤ σ b
    · have hc := perm_card_left_gt_le σ b hb
      rw [Finset.card_filter, Finset.card_filter] at hc
      calc (∑ a : Fin n, if (a : ℕ) < b ∧ (σ b : ℕ) < σ a ∧ (a : ℕ) ≤ σ a ∧ (b : ℕ) ≤ σ b
              then 1 else 0)
          ≤ ∑ a : Fin n, if (a : ℕ) < b ∧ (σ b : ℕ) < σ a then 1 else 0 := by
            apply Finset.sum_le_sum; intro a _; split_ifs <;> omega
        _ ≤ ∑ j : Fin n, if (b : ℕ) < j ∧ (σ j : ℕ) < b then 1 else 0 := hc
        _ = ∑ j : Fin n, if (b : ℕ) ≤ σ b ∧ (σ j : ℕ) < b ∧ (b : ℕ) < j then 1 else 0 := by
            apply Finset.sum_congr rfl; intro j _; split_ifs <;> omega
    · have z : ∀ a : Fin n, (if (a : ℕ) < b ∧ (σ b : ℕ) < σ a ∧ (a : ℕ) ≤ σ a ∧
          (b : ℕ) ≤ σ b then 1 else 0 : ℕ) = 0 := fun a => if_neg (by omega)
      simp only [z, Finset.sum_const_zero]
      exact Nat.zero_le _
  -- Q and C
  have hQ := perm_gap_sum σ
  have hX := perm_cross_inv_sum σ
  have hCX : (∑ a : Fin n, ∑ b : Fin n,
      if (σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ ¬((b : ℕ) < a ∧ (σ a : ℕ) < σ b) then 1 else 0) +
      (∑ a : Fin n, ∑ b : Fin n,
        if (σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ (b : ℕ) < a ∧ (σ a : ℕ) < σ b then 1 else 0) =
      k * (n - k) := by
    have hn : (∑ b : Fin n, if (σ b : ℕ) < b then 1 else 0) +
        (∑ b : Fin n, if (b : ℕ) ≤ σ b then 1 else 0) = n := by
      rw [← Finset.sum_add_distrib]
      have : ∀ b : Fin n, ((if (σ b : ℕ) < b then 1 else 0) +
          (if (b : ℕ) ≤ σ b then 1 else 0) : ℕ) = 1 := by
        intro b; split_ifs <;> omega
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one]
    have hnk : (∑ b : Fin n, if (b : ℕ) ≤ σ b then 1 else 0) = n - k := by omega
    rw [← hnk, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _
    split_ifs <;> omega
  have hsplit : (∑ a : Fin n, ∑ b : Fin n,
        if ((a : ℕ) < b ∧ (σ b : ℕ) < σ a ∧ ((σ a : ℕ) < a ↔ (σ b : ℕ) < b)) ∨
          ((σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ ¬((b : ℕ) < a ∧ (σ a : ℕ) < σ b)) then 1 else 0) ≤
      (∑ a : Fin n, ∑ b : Fin n,
        if (σ a : ℕ) < a ∧ (σ b : ℕ) < a ∧ (a : ℕ) < b then 1 else 0) +
      (∑ a : Fin n, ∑ b : Fin n,
        if (a : ℕ) < b ∧ (σ b : ℕ) < σ a ∧ (a : ℕ) ≤ σ a ∧ (b : ℕ) ≤ σ b then 1 else 0) +
      (∑ a : Fin n, ∑ b : Fin n,
        if (σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ ¬((b : ℕ) < a ∧ (σ a : ℕ) < σ b) then 1 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro b _
    exact hpt a b
  have hQsplit : (∑ a : Fin n, ∑ b : Fin n,
        if (σ a : ℕ) < a ∧ (σ b : ℕ) < a ∧ (a : ℕ) < b then 1 else 0) +
      (∑ a : Fin n, ∑ b : Fin n,
        if (a : ℕ) ≤ σ a ∧ (σ b : ℕ) < a ∧ (a : ℕ) < b then 1 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if (σ b : ℕ) < a ∧ (a : ℕ) < b then 1 else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _
    split_ifs <;> omega
  omega
