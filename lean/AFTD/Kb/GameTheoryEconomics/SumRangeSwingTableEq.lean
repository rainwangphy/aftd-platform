import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SwingTable
import AFTD.Kb.GameTheoryEconomics.SwingTableCastEqSum
import AFTD.Kb.GameTheoryEconomics.SumNotMemEqInsert

/-!
# sum_range_swing_table_eq

Topic: general_equilibrium   Node: 5d1ce8b3eb4e

For a monotone game, player i's total swing count (the sum of T(i, k) over k) equals 2 A_i - |W|, where A_i is the number of winning coalitions containing i and |W| is the number of winning coalitions.
-/

/-- For a monotone game, player `i`'s total swing count (its raw Banzhaf score) is `2 A_i - |W|`, where `A_i` is the number of winning coalitions containing `i` and `|W|` the number of winning coalitions. -/
theorem sum_range_swing_table_eq {n : ℕ} (v : Finset (Fin n) → Bool)
    (hv : ∀ S T, S ⊆ T → v S = true → v T = true) (i : Fin n) :
    ∑ k ∈ Finset.range (n + 1), (swing_table v i k : ℝ)
      = 2 * ((Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ v S = true).card : ℝ)
        - ((Finset.univ.filter fun S : Finset (Fin n) => v S = true).card : ℝ) := by
  have hcollapse : ∑ k ∈ Finset.range (n + 1), (swing_table v i k : ℝ)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∉ S),
          ((if v (insert i S) then (1:ℝ) else 0) - (if v S then 1 else 0)) := by
    simp_rw [swing_table_cast_eq_sum v hv, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    have hS : S.card ∈ Finset.range (n + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le ((Finset.card_le_univ S).trans (by simp)))
    by_cases hi : i ∉ S
    · simp only [hi, not_false_eq_true, true_and]
      rw [Finset.sum_ite_eq (Finset.range (n + 1)) S.card, if_pos hS, if_pos trivial]
    · simp [hi]
  have hW : ((Finset.univ.filter fun S : Finset (Fin n) => v S = true).card : ℝ)
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => i ∈ T), (if v T then (1:ℝ) else 0)
        + ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∉ S), (if v S then (1:ℝ) else 0) := by
    rw [Finset.sum_filter_add_sum_filter_not, Finset.card_filter]
    push_cast
    rfl
  have hA : ((Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ v S = true).card : ℝ)
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => i ∈ T), (if v T then (1:ℝ) else 0) := by
    rw [Finset.sum_filter, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro T _
    by_cases hi : i ∈ T <;> simp [hi]
  rw [hcollapse, Finset.sum_sub_distrib, sum_not_mem_eq_insert (fun T => if v T then (1:ℝ) else 0), hW, hA]
  ring
