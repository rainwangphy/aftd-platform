import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# stable_matching_of_subsingleton

Topic: matching_markets   Node: b3d5bd66d9fd

In a marriage market market with agent types M and W where M is a subsingleton (Subsingleton M), if men's preferences are irreflexive (∀ (m : M) (w : W), ¬ market.pref_m m w w), then any matching equivalence μ : M ≃ W has no blocking pairs, meaning that for all m : M and w : W, ¬ (market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w)).
-/

/-- In a subsingleton marriage market with irreflexive preferences, every matching is stable. -/
theorem stable_matching_of_subsingleton {M W : Type*} [Subsingleton M] (market : MarriageMarket M W) (h_irrefl : ∀ (m : M) (w : W), ¬ market.pref_m m w w) (μ : M ≃ W) : ∀ (m : M) (w : W), ¬ (market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w)) := by
  intro m w ⟨h1, _⟩
  have : Subsingleton W := μ.symm.subsingleton
  have hw : w = μ m := Subsingleton.elim w (μ m)
  subst hw
  exact h_irrefl m (μ m) h1
