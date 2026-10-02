import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PermInvLeftAdd

/-!
# perm_cross_inv_sum

Topic: matching_markets   Node: add0f82b27ea

For a permutation s of {0, ..., n-1}, let A be the positions a with s(a) < a. The number of pairs (a, b) with a in A, b not in A, b < a and s(a) < s(b), plus the sum of s(a) over a in A, equals the sum of a over a in A.
-/

theorem perm_cross_inv_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ a : Fin n, ∑ b : Fin n,
        if (σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ (b : ℕ) < a ∧ (σ a : ℕ) < σ b then 1 else 0) +
      ∑ a : Fin n, (if (σ a : ℕ) < a then (σ a : ℕ) else 0) =
      ∑ a : Fin n, (if (σ a : ℕ) < a then (a : ℕ) else 0) := by
  -- I a b: both in A, an inversion with a on the right
  have hpt : ∀ a : Fin n,
      (∑ b : Fin n,
          if (σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ (b : ℕ) < a ∧ (σ a : ℕ) < σ b then 1 else 0) +
        (∑ b : Fin n,
          if (σ a : ℕ) < a ∧ (σ b : ℕ) < b ∧ (b : ℕ) < a ∧ (σ a : ℕ) < σ b then 1 else 0) +
        (if (σ a : ℕ) < a then (σ a : ℕ) else 0) =
      (∑ b : Fin n,
          if (σ b : ℕ) < b ∧ (σ a : ℕ) < a ∧ (a : ℕ) < b ∧ (σ b : ℕ) < σ a then 1 else 0) +
        (if (σ a : ℕ) < a then (a : ℕ) else 0) := by
    intro a
    by_cases ha : (σ a : ℕ) < a
    · have h1 := perm_inv_left_add σ a
      rw [Finset.card_filter, Finset.card_filter] at h1
      rw [if_pos ha, if_pos ha, ← Finset.sum_add_distrib]
      have e1 : ∀ b : Fin n,
          ((if (σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ (b : ℕ) < a ∧ (σ a : ℕ) < σ b then 1 else 0) +
            (if (σ a : ℕ) < a ∧ (σ b : ℕ) < b ∧ (b : ℕ) < a ∧ (σ a : ℕ) < σ b then 1 else 0) : ℕ) =
          if (b : ℕ) < a ∧ (σ a : ℕ) < σ b then 1 else 0 := by
        intro b; split_ifs <;> omega
      have e2 : ∀ b : Fin n,
          (if (σ b : ℕ) < b ∧ (σ a : ℕ) < a ∧ (a : ℕ) < b ∧ (σ b : ℕ) < σ a then 1 else 0 : ℕ) =
          if (a : ℕ) < b ∧ (σ b : ℕ) < σ a then 1 else 0 := by
        intro b; split_ifs <;> omega
      rw [Finset.sum_congr rfl fun b _ => e1 b, Finset.sum_congr rfl fun b _ => e2 b]
      exact h1
    · rw [if_neg ha, if_neg ha]
      have z : ∀ b : Fin n, (if (σ a : ℕ) < a ∧ (b : ℕ) ≤ σ b ∧ (b : ℕ) < a ∧
          (σ a : ℕ) < σ b then 1 else 0 : ℕ) = 0 := fun b => if_neg (by omega)
      have z2 : ∀ b : Fin n, (if (σ a : ℕ) < a ∧ (σ b : ℕ) < b ∧ (b : ℕ) < a ∧
          (σ a : ℕ) < σ b then 1 else 0 : ℕ) = 0 := fun b => if_neg (by omega)
      have z3 : ∀ b : Fin n, (if (σ b : ℕ) < b ∧ (σ a : ℕ) < a ∧ (a : ℕ) < b ∧
          (σ b : ℕ) < σ a then 1 else 0 : ℕ) = 0 := fun b => if_neg (by omega)
      simp only [z, z2, z3, Finset.sum_const_zero]
      rfl
  have hsum := Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hpt a
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hswap : (∑ a : Fin n, ∑ b : Fin n,
      if (σ b : ℕ) < b ∧ (σ a : ℕ) < a ∧ (a : ℕ) < b ∧ (σ b : ℕ) < σ a then 1 else 0) =
      ∑ a : Fin n, ∑ b : Fin n,
        if (σ a : ℕ) < a ∧ (σ b : ℕ) < b ∧ (b : ℕ) < a ∧ (σ a : ℕ) < σ b then 1 else 0 :=
    Finset.sum_comm
  rw [hswap] at hsum
  omega
