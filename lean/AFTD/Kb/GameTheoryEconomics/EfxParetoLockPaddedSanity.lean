import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPartialNat
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility
import AFTD.Kb.GameTheoryEconomics.EfxPartialScaledTail
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockPaddedValues
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockPaddedOwner
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockPaddedBaseline
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockStrictMargins
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockBaseline
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockUtility

/-!
# efx_pareto_lock_padded_sanity

Topic: fair_division   Node: 515d53445cdc

Provenance: helper lemma. Arbitrary source-bundle padding of the OP-7 Pareto-maximal locked-good obstruction, experiments 11497 and 11498.

For every k the padded starting allocation is partial EFX and has the claimed baseline utilities.
-/

theorem efx_pareto_lock_padded_sanity (k : ℕ) :
  efx_partial_nat (efx_pareto_lock_padded_values k) (efx_pareto_lock_padded_owner k) ∧
  ∀ i : Fin 4, efx_partial_nat_utility (efx_pareto_lock_padded_values k) (efx_pareto_lock_padded_owner k) i =
    efx_pareto_lock_padded_baseline k i := by
  have hutil : ∀ i : Fin 4, efx_partial_nat_utility (efx_pareto_lock_padded_values k) (efx_pareto_lock_padded_owner k) i
      = (k+k+1) * efx_pareto_lock_baseline i + (if i = 0 ∨ i = 1 then k else 0) := by
    intro i
    unfold efx_partial_nat_utility efx_pareto_lock_padded_values efx_pareto_lock_padded_owner efx_partial_scaled_tail
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    have hbase : (∑ x : Fin 8, if ![1,0,0,0,1,2,4,3] x = i.castSucc then efx_pareto_lock_values i x else 0) = efx_pareto_lock_baseline i := by
      fin_cases i <;> decide
    have hmul : (∑ x : Fin 8, if ![1,0,0,0,1,2,4,3] x = i.castSucc then (k+k+1) * efx_pareto_lock_values i x else 0) = (k+k+1) * efx_pareto_lock_baseline i := by
      rw [← hbase, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hc : ![1,0,0,0,1,2,4,3] x = i.castSucc <;> simp [hc]
    have htail : (∑ x : Fin (k+k), if (if (x:ℕ) < k then (0:Fin 5) else 1) = i.castSucc then (1:ℕ) else 0)
        = (if i = 0 ∨ i = 1 then k else 0) := by
      rw [Fin.sum_univ_add]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      have h2 : ∀ x : Fin k, ¬ (k + (x:ℕ) < k) := by intro x; omega
      simp only [Fin.isLt, if_true, h2, if_false]
      fin_cases i <;> simp [Finset.sum_const]
    rw [hmul, htail]
  have hutil_old : ∀ i : Fin 4, efx_pareto_lock_utility ![1,0,0,0,1,2,4,3] i = efx_pareto_lock_baseline i := by
    intro i; fin_cases i <;> decide
  have hS : ∀ i j : Fin 4,
      (∑ h : Fin (8+(k+k)), if efx_pareto_lock_padded_owner k h = j.castSucc then efx_pareto_lock_padded_values k i h else 0)
      = (k+k+1) * (∑ x : Fin 8, if ![1,0,0,0,1,2,4,3] x = j.castSucc then efx_pareto_lock_values i x else 0)
        + (if j = 0 ∨ j = 1 then k else 0) := by
    intro i j
    unfold efx_pareto_lock_padded_owner efx_pareto_lock_padded_values efx_partial_scaled_tail
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hc : ![1,0,0,0,1,2,4,3] x = j.castSucc <;> simp [hc]
    · rw [Fin.sum_univ_add]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      have h2 : ∀ x : Fin k, ¬ (k + (x:ℕ) < k) := by intro x; omega
      simp only [Fin.isLt, if_true, h2, if_false]
      fin_cases j <;> simp [Finset.sum_const]
  constructor
  · intro i j hij
    rw [Fin.forall_fin_add]
    constructor
    · intro g' hg
      rw [hS i j, hutil i]
      simp only [efx_pareto_lock_padded_owner, Fin.addCases_left] at hg
      have hm1 := efx_pareto_lock_strict_margins.1 i j hij g' hg
      rw [hutil_old i] at hm1
      have hv : efx_pareto_lock_padded_values k i (Fin.castAdd (k+k) g') = (k+k+1) * efx_pareto_lock_values i g' := by
        unfold efx_pareto_lock_padded_values efx_partial_scaled_tail
        simp only [Fin.addCases_left]
      rw [hv]
      have hTj : (if j = 0 ∨ j = 1 then k else 0) ≤ k := by
        by_cases hj : j = 0 ∨ j = 1 <;> simp [hj]
      have hmul : (k+k+1) * ((∑ x : Fin 8, if ![1,0,0,0,1,2,4,3] x = j.castSucc then efx_pareto_lock_values i x else 0) + 6)
        ≤ (k+k+1) * (efx_pareto_lock_baseline i + efx_pareto_lock_values i g') := by
        apply Nat.mul_le_mul_left
        linarith
      rw [Nat.mul_add, Nat.mul_add] at hmul
      have hk : k ≤ (k+k+1) * 6 := by omega
      omega
    · intro g' hg
      rw [hS i j, hutil i]
      simp only [efx_pareto_lock_padded_owner, Fin.addCases_right] at hg
      have hj : j = 0 ∨ j = 1 := by
        by_cases hlt : (g':ℕ) < k
        · left
          simp [hlt] at hg
          exact Fin.castSucc_inj.mp (hg.symm.trans rfl)
        · right
          simp [hlt] at hg
          exact Fin.castSucc_inj.mp (hg.symm.trans rfl)
      have hm2 := efx_pareto_lock_strict_margins.2 i j hij hj
      rw [hutil_old i] at hm2
      have hv : efx_pareto_lock_padded_values k i (Fin.natAdd 8 g') = 1 := by
        unfold efx_pareto_lock_padded_values efx_partial_scaled_tail
        simp only [Fin.addCases_right]
      rw [hv]
      simp only [hj, if_true]
      have hmul : (k+k+1) * ((∑ x : Fin 8, if ![1,0,0,0,1,2,4,3] x = j.castSucc then efx_pareto_lock_values i x else 0) + 5)
        ≤ (k+k+1) * (efx_pareto_lock_baseline i) := by
        apply Nat.mul_le_mul_left
        linarith
      rw [Nat.mul_add] at hmul
      omega
  · intro i
    rw [hutil i]
    rfl
