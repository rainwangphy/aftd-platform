import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SwingTable
import AFTD.Kb.GameTheoryEconomics.SwingTableCastEqSum
import AFTD.Kb.GameTheoryEconomics.SumNotMemCardEqInsert

/-!
# sum_swing_table_eq

Topic: general_equilibrium   Node: 4fd50f38d4f2

For a monotone game, the sum over all players of T(i, k) equals (k+1) w(k+1) - (n-k) w(k), where w(k) is the number of winning coalitions of size k.
-/

/-- For a monotone game, the swings at size `k` summed over all players equal `(k+1) w_{k+1} - (n-k) w_k`, where `w_k` is the number of winning coalitions of size `k`. -/
theorem sum_swing_table_eq {n : ℕ} (v : Finset (Fin n) → Bool)
    (hv : ∀ S T, S ⊆ T → v S = true → v T = true) (k : ℕ) :
    ∑ i, (swing_table v i k : ℝ)
      = (k + 1) * ((Finset.univ.filter fun S : Finset (Fin n) => S.card = k + 1 ∧ v S = true).card : ℝ)
        - (n - k) * ((Finset.univ.filter fun S : Finset (Fin n) => S.card = k ∧ v S = true).card : ℝ) := by
  simp_rw [swing_table_cast_eq_sum v hv, Finset.sum_sub_distrib]
  simp_rw [sum_not_mem_card_eq_insert (fun T => if v T then (1:ℝ) else 0)]
  congr 1
  · rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hc : T.card = k + 1 <;> by_cases hvT : v T = true
    · simp [hc, hvT]
    · simp [hc, hvT]
    · simp [hc, hvT]
    · simp [hc, hvT]
  · rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hc : S.card = k <;> by_cases hvS : v S = true
    · have hle : S.card ≤ n := (Finset.card_le_univ S).trans (by simp)
      have hcomp : (Finset.univ.filter fun i : Fin n => i ∉ S).card = n - k := by
        rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simp [hc]
      simp only [hc, hvS, and_true, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcomp, Nat.cast_sub (hc ▸ hle)]
      simp
    · simp [hc, hvS]
    · simp [hc, hvS]
    · simp [hc, hvS]
