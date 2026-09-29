import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# stable_matching_not_pref_of_pref

Topic: matching_markets   Node: 8aeb0130161c

In a marriage market market with agent types M and W, if a matching equivalence μ : M ≃ W has no blocking pairs (that is, for all m : M and w : W, ¬ (market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w))), and a man m : M strictly prefers woman w : W to his assigned partner μ m under market.pref_m, then woman w does not strictly prefer m to her assigned partner μ.symm w under market.pref_w.
-/

/-- In a stable matching, if a man prefers another woman to his partner, that woman does not prefer him to hers. -/
theorem stable_matching_not_pref_of_pref {M W : Type*} (market : MarriageMarket M W) (μ : M ≃ W) (h_stable : ∀ (m : M) (w : W), ¬ (market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w))) (m : M) (w : W) (h : market.pref_m m w (μ m)) : ¬ market.pref_w w m (μ.symm w) := fun hw => h_stable m w ⟨h, hw⟩
