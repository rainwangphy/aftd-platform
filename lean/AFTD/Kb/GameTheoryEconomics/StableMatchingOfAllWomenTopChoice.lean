import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# stable_matching_of_all_women_top_choice

Topic: matching_markets   Node: 99d0913ecbc6

In a marriage market market with agent types M and W, if every woman w : W is matched under equivalence μ : M ≃ W to a man μ.symm w such that for all men m : M she does not strictly prefer m to μ.symm w (that is, ∀ (w : W) (m : M), ¬ market.pref_w w m (μ.symm w)), then the matching has no blocking pairs, meaning that for all m : M and w : W, ¬ (market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w)).
-/

/-- A matching in which every woman receives her top choice has no blocking pairs. -/
theorem stable_matching_of_all_women_top_choice {M W : Type*} (market : MarriageMarket M W) (μ : M ≃ W) (h_top : ∀ (w : W) (m : M), ¬ market.pref_w w m (μ.symm w)) : ∀ (m : M) (w : W), ¬ (market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w)) := fun _ w ⟨_, hw⟩ => h_top w _ hw
