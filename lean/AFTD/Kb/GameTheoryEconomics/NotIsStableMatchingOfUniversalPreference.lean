import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket
import AFTD.Kb.GameTheoryEconomics.IsStableMatching

/-!
# not_is_stable_matching_of_universal_preference

Topic: matching_markets   Node: 8330d2c0302a

Provenance: helper lemma. sanity check of the definition is_stable_matching (College Admissions and the Stability of Marriage, 1962)

In the marriage market on M and W whose two preference relations are identically true, so that every agent strictly prefers everyone to everyone, no matching μ : M ≃ W is stable, provided M is inhabited.
-/

/-- Stability is not vacuous: in a market where every agent strictly prefers everyone to everyone, no matching is stable, provided there is at least one man. -/
theorem not_is_stable_matching_of_universal_preference {M W : Type*}
    (m : M) (μ : M ≃ W) :
    ¬ is_stable_matching
      (MarriageMarket.mk (fun _ _ _ => True) (fun _ _ _ => True)) μ := fun hs => hs m (μ m) ⟨trivial, trivial⟩
