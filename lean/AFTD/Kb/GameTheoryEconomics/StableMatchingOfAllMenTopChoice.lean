import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# stable_matching_of_all_men_top_choice

Topic: matching_markets   Node: d00f09fba50d

In a marriage market market with agent types M and W, if every man m : M is matched under equivalence μ : M ≃ W to a woman μ m such that for all women w : W he does not strictly prefer w to μ m (that is, ∀ (m : M) (w : W), ¬ market.pref_m m w (μ m)), then the matching has no blocking pairs, meaning that for all m : M and w : W, ¬ (market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w)).
-/

/-- A matching in which every man receives his top choice has no blocking pairs. -/
theorem stable_matching_of_all_men_top_choice {M W : Type*} (market : MarriageMarket M W) (μ : M ≃ W) (h_top : ∀ (m : M) (w : W), ¬ market.pref_m m w (μ m)) : ∀ (m : M) (w : W), ¬ (market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w)) := by
  intro m w ⟨h1, _⟩
  exact h_top m w h1
