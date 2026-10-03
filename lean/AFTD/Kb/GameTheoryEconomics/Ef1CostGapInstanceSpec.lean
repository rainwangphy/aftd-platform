import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.Ef1CostGapInstance
import AFTD.Kb.GameTheoryEconomics.Ef1costEf1OfPair
import AFTD.Kb.GameTheoryEconomics.Ef1costFinTwoCases
import AFTD.Kb.GameTheoryEconomics.Ef1costSocialCostEq
import AFTD.Kb.GameTheoryEconomics.IsNormalizedChoresInstance
import AFTD.Kb.GameTheoryEconomics.OptEf1SocialCost
import AFTD.Kb.GameTheoryEconomics.OptSocialCost
import AFTD.Kb.GameTheoryEconomics.SocialCost

/-!
# ef1_cost_gap_instance_spec

Topic: fair_division   Node: cf94d73efda4

In the instance (0, 1/2, 1/2), (1/3 - 2d, 1/3 + d, 1/3 + d) with 0 < d <= 1/6, the optimal social cost is 2/3 + 2d and the best EF1 social cost is 5/6 + d, a gap of 1/6 - d.
-/

/-- **Lower-bound instance.** For `0 < δ ≤ 1/6`, `ef1_cost_gap_instance δ` is a normalised two-agent instance with `OPT = 2/3 + 2δ`, optimal EF1 social cost `5/6 + δ`, hence gap `1/6 - δ`. -/
theorem ef1_cost_gap_instance_spec (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 6) :
    is_normalized_chores_instance (ef1_cost_gap_instance δ) ∧
      opt_social_cost (ef1_cost_gap_instance δ) = 2 / 3 + 2 * δ ∧
      opt_ef1_social_cost (ef1_cost_gap_instance δ) = 5 / 6 + δ ∧
      opt_ef1_social_cost (ef1_cost_gap_instance δ) - opt_social_cost (ef1_cost_gap_instance δ)
        = 1 / 6 - δ := by
  classical
  set c := ef1_cost_gap_instance δ with hcdef
  have c00 : c 0 0 = 0 := by simp [hcdef, ef1_cost_gap_instance]
  have c01 : c 0 1 = 1 / 2 := by simp [hcdef, ef1_cost_gap_instance]
  have c02 : c 0 2 = 1 / 2 := by simp [hcdef, ef1_cost_gap_instance]
  have c10 : c 1 0 = 1 / 3 - 2 * δ := by simp [hcdef, ef1_cost_gap_instance]
  have c11 : c 1 1 = 1 / 3 + δ := by simp [hcdef, ef1_cost_gap_instance]
  have c12 : c 1 2 = 1 / 3 + δ := by simp [hcdef, ef1_cost_gap_instance]
  have hall : ∀ i : Fin 2, ∀ j : Fin 3, c i j = ![![0, 1/2, 1/2], ![1/3 - 2 * δ, 1/3 + δ, 1/3 + δ]] i j :=
    fun i j => rfl
  have hfin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := ef1cost_fin_two_cases 0 1 (by decide)
  have hnorm : is_normalized_chores_instance c := by
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rcases hfin2 i with rfl | rfl <;> fin_cases j <;> simp [hcdef, ef1_cost_gap_instance] <;>
        linarith
    · rcases hfin2 i with rfl | rfl <;> simp [Fin.sum_univ_three, c00, c01, c02, c10, c11, c12] <;>
        ring
  have hnn : ∀ i j, 0 ≤ c i j := hnorm.1
  have lo0 : ∀ i, 0 ≤ c i 0 := fun i => hnn i 0
  have lo1 : ∀ i, 1 / 3 + δ ≤ c i 1 := by
    intro i; rcases hfin2 i with rfl | rfl
    · rw [c01]; linarith
    · rw [c11]
  have lo2 : ∀ i, 1 / 3 + δ ≤ c i 2 := by
    intro i; rcases hfin2 i with rfl | rfl
    · rw [c02]; linarith
    · rw [c12]
  -- OPT
  have hopt : opt_social_cost c = 2 / 3 + 2 * δ := by
    apply le_antisymm
    · have := ciInf_le (Set.finite_range (fun σ : Fin 3 → Fin 2 => social_cost c σ)).bddBelow
        (![0, 1, 1] : Fin 3 → Fin 2)
      refine le_trans this (le_of_eq ?_)
      rw [ef1cost_social_cost_eq, Fin.sum_univ_three]
      simp [c00, c11, c12]
      ring
    · refine le_ciInf (fun σ => ?_)
      rw [ef1cost_social_cost_eq, Fin.sum_univ_three]
      linarith [lo0 (σ 0), lo1 (σ 1), lo2 (σ 2)]
  -- optimal EF1
  have hef1 : opt_ef1_social_cost c = 5 / 6 + δ := by
    apply IsLeast.csInf_eq
    constructor
    · -- the allocation giving chores 0, 2 to agent 0 and chore 1 to agent 1
      refine ⟨fun j => if j ∈ ({0, 2} : Finset (Fin 3)) then 0 else 1, ?_, ?_⟩
      · apply ef1cost_ef1_of_pair c 0 1 (by decide)
        · right
          refine ⟨2, by simp, ?_⟩
          rw [Finset.sum_pair (by decide), c00]
          simp only [add_sub_cancel_right]
          exact Finset.sum_nonneg (fun j _ => hnn 0 j)
        · right
          have hc : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide
          refine ⟨1, by simp [hc], ?_⟩
          rw [hc, Finset.sum_singleton, sub_self]
          exact Finset.sum_nonneg (fun j _ => hnn 1 j)
      · show social_cost c _ = _
        rw [ef1cost_social_cost_eq, Fin.sum_univ_three]
        simp [c00, c11, c02]
        ring
    · rintro _ ⟨σ, hσ, rfl⟩
      rw [ef1cost_social_cost_eq, Fin.sum_univ_three]
      by_cases h12 : σ 1 = 1 ∧ σ 2 = 1
      · exfalso
        obtain ⟨h1, h2⟩ := h12
        have hb : bundle_of σ 0 = (bundle_of σ 1)ᶜ := by
          ext j
          simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
          rcases hfin2 (σ j) with h | h <;> simp [h]
        have hsum : additive_valuation (c 1) (bundle_of σ 1) +
            additive_valuation (c 1) (bundle_of σ 0) = 1 := by
          rw [hb, additive_valuation, additive_valuation, Finset.sum_add_sum_compl]
          exact hnorm.2 1
        have hbig : 2 / 3 + 2 * δ ≤ additive_valuation (c 1) (bundle_of σ 1) := by
          have hsub : ({1, 2} : Finset (Fin 3)) ⊆ bundle_of σ 1 := by
            intro j hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hj with rfl | rfl
            · exact h1
            · exact h2
          have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := c 1)
            (fun j _ _ => hnn 1 j)
          rw [Finset.sum_pair (by decide), c11, c12] at this
          unfold additive_valuation
          linarith
        have hmax : ∀ e, c 1 e ≤ 1 / 3 + δ := by
          intro e
          fin_cases e
          · show c 1 0 ≤ _; rw [c10]; linarith
          · show c 1 1 ≤ _; rw [c11]
          · show c 1 2 ≤ _; rw [c12]
        rcases hσ 1 0 with h | ⟨e, -, h⟩
        · linarith
        · linarith [hmax e]
      · rw [not_and_or] at h12
        have k1 : ∀ i, σ 1 = i → i ≠ 1 → c (σ 1) 1 = 1 / 2 := by
          intro i hi hne
          rcases hfin2 i with rfl | rfl
          · rw [hi, c01]
          · exact absurd rfl hne
        have k2 : ∀ i, σ 2 = i → i ≠ 1 → c (σ 2) 2 = 1 / 2 := by
          intro i hi hne
          rcases hfin2 i with rfl | rfl
          · rw [hi, c02]
          · exact absurd rfl hne
        rcases h12 with h | h
        · linarith [k1 (σ 1) rfl h, lo0 (σ 0), lo2 (σ 2)]
        · linarith [k2 (σ 2) rfl h, lo0 (σ 0), lo1 (σ 1)]
  refine ⟨hnorm, hopt, hef1, ?_⟩
  rw [hopt, hef1]
  ring
