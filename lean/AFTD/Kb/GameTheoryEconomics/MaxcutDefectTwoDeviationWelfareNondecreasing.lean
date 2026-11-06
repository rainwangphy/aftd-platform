import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfareSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilitySumSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_defect_two_deviation_welfare_nondecreasing

Topic: equilibria   Node: 41c258b1f9c4

Provenance: helper lemma. Coalitional cut-change identities are discussed in https://www.mdpi.com/2227-7390/12/4/604 and arXiv:2610.04948.

A strong deviation cannot decrease the cut value when every member of the deviating coalition initially has at most two same-colored neighbors. No Nash assumption or bound outside the coalition is needed.
-/

set_option maxHeartbeats 2000000

theorem maxcut_defect_two_deviation_welfare_nondecreasing
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ τ : V → Fin k) (C : Finset V)
    (hdefect : ∀ v ∈ C, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2)
    (hdev : is_maxcut_strong_deviation G σ C τ) :
    maxcut_welfare G σ ≤ maxcut_welfare G τ := by
  classical
  obtain ⟨hne, hout, hgain⟩ := hdev
  have hgains : ∑ v ∈ C, maxcut_utility G σ v + C.card ≤
      ∑ v ∈ C, maxcut_utility G τ v := by
    have := Finset.sum_le_sum fun v hv => Nat.succ_le_of_lt (hgain v hv)
    simpa [Finset.sum_add_distrib] using this
  have hu_σ := maxcut_utility_sum_split G σ C
  have hu_τ := maxcut_utility_sum_split G τ C
  have hw_σ := maxcut_welfare_split G σ C
  have hw_τ := maxcut_welfare_split G τ C
  have hC : (∑ v ∈ Cᶜ, ∑ w ∈ Cᶜ, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ)) =
      ∑ v ∈ Cᶜ, ∑ w ∈ Cᶜ, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.mem_compl] at hv hw
    rw [hout v hv, hout w hw]
  have hM (ρ : V → Fin k) :
      (∑ v ∈ C, ∑ w ∈ C, (if G.Adj v w ∧ ρ w = ρ v then 1 else 0 : ℕ)) +
        (∑ v ∈ C, ∑ w ∈ C, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ)) =
        ∑ v ∈ C, ∑ w ∈ C, (if G.Adj v w then 1 else 0 : ℕ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    by_cases h : G.Adj v w
    · by_cases heq : ρ w = ρ v
      · simp [h, heq]
      · simp [h, heq]
    · simp [h]
  have hM_σ := hM σ
  have hM_τ := hM τ
  have hbound : (∑ v ∈ C, ∑ w ∈ C, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ)) ≤ 2 * C.card := by
    calc
      _ ≤ ∑ v ∈ C, 2 := by
        apply Finset.sum_le_sum
        intro v hv
        have hsub : (C.filter fun w => G.Adj v w ∧ σ w = σ v) ⊆
            Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
          exact hw.2
        have hh := le_trans (Finset.card_le_card hsub) (hdefect v hv)
        simpa only [Finset.card_filter] using hh
      _ = 2 * C.card := by simp [Nat.mul_comm]
  omega
