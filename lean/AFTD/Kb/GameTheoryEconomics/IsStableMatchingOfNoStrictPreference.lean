import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket
import AFTD.Kb.GameTheoryEconomics.IsStableMatching

/-!
# is_stable_matching_of_no_strict_preference

Topic: matching_markets   Node: cea1b719721e

Provenance: helper lemma. sanity check of the definition is_stable_matching (College Admissions and the Stability of Marriage, 1962)

In the marriage market on M and W whose two preference relations are identically false, so that no agent strictly prefers anyone to anyone, every matching μ : M ≃ W is stable.
-/

/-- Stability is satisfiable: in a market where nobody strictly prefers anyone to anyone, every matching is stable. -/
theorem is_stable_matching_of_no_strict_preference {M W : Type*}
    (μ : M ≃ W) :
    is_stable_matching
      (MarriageMarket.mk (fun _ _ _ => False) (fun _ _ _ => False)) μ := fun _ _ h => h.1
