import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectTwoDeviationWelfareNondecreasing
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilitySumSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfareSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# maxcut_defect_two_equal_welfare_deviation_structure

Topic: equilibria   Node: 784b0dfd1981

Provenance: helper lemma. Equality case of the coalition incidence-count argument.

If a strong deviation from coalition defect at most two preserves welfare, every deviator has defect two before and one after, every old monochromatic edge touching the coalition is internal, and every new monochromatic edge touching it is a boundary edge.
-/

set_option maxHeartbeats 2000000

theorem maxcut_defect_two_equal_welfare_deviation_structure
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ τ : V → Fin k) (C : Finset V)
    (hdefect : ∀ v ∈ C, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2)
    (hdev : is_maxcut_strong_deviation G σ C τ)
    (heq : maxcut_welfare G σ = maxcut_welfare G τ) :
    (∀ v ∈ C, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 ∧
      (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card = 1) ∧
    (∀ v ∈ C, ∀ w, G.Adj v w → σ v = σ w → w ∈ C) ∧
    (∀ v ∈ C, ∀ w ∈ C, G.Adj v w → τ v ≠ τ w) := by
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
  have hzero : (∑ v ∈ C, ∑ w ∈ C, (if G.Adj v w ∧ τ w = τ v then 1 else 0 : ℕ)) = 0 := by omega
  have hfull : (∑ v ∈ C, ∑ w ∈ C, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ)) = 2 * C.card := by omega
  have hgain_eq : ∑ v ∈ C, maxcut_utility G τ v = (∑ v ∈ C, maxcut_utility G σ v) + C.card := by omega
  have hold_bound (v : V) (hv : v ∈ C) :
      (C.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2 := by
    apply le_trans _ (hdefect v hv)
    apply Finset.card_le_card
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact hw.2
  have hold_full (v : V) (hv : v ∈ C) :
      (C.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 := by
    have hle := hold_bound v hv
    by_contra hne
    have hlt : (C.filter fun w => G.Adj v w ∧ σ w = σ v).card < 2 := by omega
    have hsumlt : (∑ v ∈ C, (C.filter fun w => G.Adj v w ∧ σ w = σ v).card) < ∑ v ∈ C, 2 := by
      apply Finset.sum_lt_sum
      · exact fun u hu => hold_bound u hu
      · exact ⟨v, hv, hlt⟩
    simp only [Finset.card_filter] at hsumlt
    simp only [Finset.sum_const, nsmul_eq_mul] at hsumlt
    rw [hfull] at hsumlt
    simp only [Nat.cast_id, Nat.mul_comm, lt_self_iff_false] at hsumlt
  have hgain_one (v : V) (hv : v ∈ C) : maxcut_utility G τ v = maxcut_utility G σ v + 1 := by
    have hle := Nat.succ_le_of_lt (hgain v hv)
    by_contra hne
    have hlt : maxcut_utility G σ v + 1 < maxcut_utility G τ v := by omega
    have hsumlt : (∑ v ∈ C, (maxcut_utility G σ v + 1)) < ∑ v ∈ C, maxcut_utility G τ v := by
      apply Finset.sum_lt_sum
      · intro u hu
        exact Nat.succ_le_of_lt (hgain u hu)
      · exact ⟨v, hv, hlt⟩
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsumlt
    rw [hgain_eq] at hsumlt
    simp only [Nat.cast_id, lt_self_iff_false] at hsumlt
  have hold_all (v : V) (hv : v ∈ C) :
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 := by
    have hsub : (C.filter fun w => G.Adj v w ∧ σ w = σ v) ⊆
        Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
      exact hw.2
    have hle := Finset.card_le_card hsub
    have hh := hold_full v hv
    have hd := hdefect v hv
    omega
  have hnew_all (v : V) (hv : v ∈ C) :
      (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card = 1 := by
    have huσ := maxcut_utility_add_monochromatic_card G σ v
    have huτ := maxcut_utility_add_monochromatic_card G τ v
    have ha := hold_all v hv
    have hg := hgain_one v hv
    omega
  refine ⟨fun v hv => ⟨hold_all v hv, hnew_all v hv⟩, ?_, ?_⟩
  · intro v hv w hadj heqvw
    by_contra hwn
    have hs : (C.filter fun w => G.Adj v w ∧ σ w = σ v) ⊂
        Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
        exact hz.2
      · intro heq
        have hin : w ∈ Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v := by
          simp [hadj, heqvw.symm]
        have : w ∈ C.filter fun w => G.Adj v w ∧ σ w = σ v := heq.symm ▸ hin
        exact hwn (Finset.mem_filter.mp this).1
    have hh := Finset.card_lt_card hs
    have hi := hold_full v hv
    have ha := hold_all v hv
    omega
  · intro v hv w hw hadj heqvw
    have hpos : 0 < (∑ v ∈ C, ∑ w ∈ C, (if G.Adj v w ∧ τ w = τ v then 1 else 0 : ℕ)) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => Nat.zero_le _) hv)
      apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => Nat.zero_le _) hw)
      simp [hadj, heqvw.symm]
    omega
