import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsExAnteProportionalChores
import AFTD.Kb.GameTheoryEconomics.IsExPostAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# ex_post_one_mms_chore_lottery_single_agent

Topic: fair_division   Node: 72409dcf2540

Provenance: helper lemma. folklore

For a single agent (n = 1) and any m indivisible chores with nonnegative additive costs c, there exists an allocation lottery that is simultaneously ex-ante proportional and ex-post 1-MMS.
-/

/-- For a single agent (n = 1), there exists an ex-ante proportional and ex-post 1-MMS chore lottery. -/
theorem ex_post_one_mms_chore_lottery_single_agent
    (m : ℕ) (c : Fin 1 → Fin m → ℝ) (hc : ∀ i e, 0 ≤ c i e) :
    ∃ p ∈ stdSimplex ℝ (Fin m → Fin 1),
      is_ex_ante_proportional_chores c p ∧
      is_ex_post_alpha_mms_chores 1 c p := by
  refine ⟨fun _ => (1:ℝ), ?_, ?_, ?_⟩
  · constructor
    · intro x; norm_num
    · simp
  · intro i
    fin_cases i
    simp [additive_valuation, bundle_of]
  · intro σ hp i
    have h : chore_maximin_share 1 (c i) = ∑ j, c i j := by
      simp [chore_maximin_share, additive_valuation, bundle_of]
    rw [h]
    simp only [additive_valuation, bundle_of]
    fin_cases i
    simp only [one_mul]
    exact Finset.sum_le_univ_sum_of_nonneg (fun x => hc 0 x)
