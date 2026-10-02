import AFTD.Prelude

/-!
# perm_gap_sum

Topic: matching_markets   Node: 1bdc6ae3372f

For a permutation s of {0, ..., n-1}, the number of pairs (a, b) with s(b) < a < b, plus the number of positions b with s(b) < b, plus the sum of s(b) over those b, equals the sum of b over those b.
-/

theorem perm_gap_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ a : Fin n, ∑ b : Fin n, if (σ b : ℕ) < a ∧ (a : ℕ) < b then 1 else 0) +
      (∑ b : Fin n, if (σ b : ℕ) < b then 1 else 0) +
      ∑ b : Fin n, (if (σ b : ℕ) < b then (σ b : ℕ) else 0) =
      ∑ b : Fin n, (if (σ b : ℕ) < b then (b : ℕ) else 0) := by
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hc : (∑ a : Fin n, if (σ b : ℕ) < a ∧ (a : ℕ) < b then 1 else 0) =
      (b : ℕ) - σ b - 1 := by
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun a : Fin n => (σ b : ℕ) < a ∧ (a : ℕ) < b) =
        Finset.Ioo (σ b) b := by
      ext a
      simp
    rw [this, Fin.card_Ioo]
  rw [hc]
  split_ifs <;> omega
