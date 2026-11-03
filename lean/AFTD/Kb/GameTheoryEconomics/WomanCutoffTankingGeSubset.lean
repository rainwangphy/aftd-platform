import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WomanCutoffTanking
import AFTD.Kb.GameTheoryEconomics.IsStableMatching
import AFTD.Kb.GameTheoryEconomics.MarriageMarket
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair
import AFTD.Kb.GameTheoryEconomics.MoveToBottom

/-!
# woman_cutoff_tanking_ge_subset

Topic: matching_markets   Node: 47e12e78ee71

Provenance: helper lemma. arXiv:2610.42105 Lemma 4.1

In a marriage market, any matching μ stable in market that assigns woman w a partner weakly preferred to t (that is, ¬ market.pref_w w t (μ.symm w)) remains stable after t-cutoff tanking by w.
-/

/-- A blocking pair in the t-cutoff-tanked market, when `w` weakly prefers her own
partner over `t`, is already a blocking pair in the original market. -/
private theorem woman_cutoff_tanking_ge_subset_aux {M W : Type*}
    (market : MarriageMarket M W) (w : W) (t : M) (μ : M ≃ W)
    (h_ge : ¬ market.pref_w w t (μ.symm w)) :
    ∀ (m : M) (w' : W),
      is_blocking_pair (woman_cutoff_tanking market w t) μ m w' →
      is_blocking_pair market μ m w' := by
  intro m w' hbp
  obtain ⟨h1, h2⟩ := hbp
  refine ⟨?_, h2⟩
  by_cases h : market.pref_w w t m
  · have hmw : μ m ≠ w := by
      intro heq
      apply h_ge
      have : μ.symm w = m := by rw [← heq]; simp
      rwa [this]
    by_cases hw' : w' = w
    · subst hw'
      simp [woman_cutoff_tanking, h, move_to_bottom] at h1
    · simp [woman_cutoff_tanking, h, move_to_bottom, hmw, hw'] at h1
      exact h1
  · simpa [woman_cutoff_tanking, h] using h1

/-- A stable matching assigning woman w at least t survives t-cutoff tanking by w. -/
theorem woman_cutoff_tanking_ge_subset {M W : Type*}
    (market : MarriageMarket M W) (w : W) (t : M) (μ : M ≃ W)
    (h_stable : is_stable_matching market μ)
    (h_ge : ¬ market.pref_w w t (μ.symm w)) :
    is_stable_matching (woman_cutoff_tanking market w t) μ := by
  intro m w' hbp
  exact h_stable m w' (woman_cutoff_tanking_ge_subset_aux market w t μ h_ge m w' hbp)
