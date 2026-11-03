import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WomanCutoffTanking
import AFTD.Kb.GameTheoryEconomics.MarriageMarket
import AFTD.Kb.GameTheoryEconomics.MoveToBottom
import AFTD.Kb.GameTheoryEconomics.IsStableMatching
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair

/-!
# woman_cutoff_tanking_is_stable_of_ge

Topic: matching_markets   Node: 141291fd68c0

Provenance: helper lemma. arXiv:2610.42105 Appendix A.2

In a marriage market where woman w's preferences are transitive, any matching μ stable after t-cutoff tanking by w that assigns w a partner weakly preferred to t is also stable in the original market.
-/

/-- A matching stable after t-cutoff tanking by w that assigns w at least t is stable in the original market. -/
theorem woman_cutoff_tanking_is_stable_of_ge {M W : Type*}
    (market : MarriageMarket M W) (w : W) (t : M)
    (hw_trans : ∀ a b c : M, market.pref_w w a b → market.pref_w w b c → market.pref_w w a c)
    (μ : M ≃ W)
    (h_tank_stable : is_stable_matching (woman_cutoff_tanking market w t) μ)
    (h_ge : ¬ market.pref_w w t (μ.symm w)) :
    is_stable_matching market μ := by
  intro m' w' h_bp
  have h_tank_not_bp := h_tank_stable m' w'
  rcases h_bp with ⟨h_m_pref, h_w_pref⟩
  apply h_tank_not_bp
  refine ⟨?_, h_w_pref⟩
  dsimp [woman_cutoff_tanking]
  by_cases h1 : market.pref_w w t m'
  · rw [if_pos h1]
    dsimp [move_to_bottom]
    by_cases h2 : w' = w
    · rw [if_pos h2]
      rw [h2] at h_w_pref
      exact False.elim (h_ge (hw_trans t m' (μ.symm w) h1 h_w_pref))
    · rw [if_neg h2]
      by_cases h3 : μ m' = w
      · rw [if_pos h3]
        trivial
      · rw [if_neg h3]
        exact h_m_pref
  · rw [if_neg h1]
    exact h_m_pref
