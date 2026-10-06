import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair

/-!
# is_stable_matching

Topic: matching_markets   Node: 66d97a46dd60

Provenance: formalization of a published result. Source: College Admissions and the Stability of Marriage (1962): stable matching; standard textbook definition (matching markets)

In a marriage market with agent types M and W, a matching μ : M ≃ W is stable when no man m and woman w form a blocking pair, that is, when for every m and every w it is not the case that m prefers w to μ m and w prefers m to μ.symm w.
-/

/-- A matching is stable when no pair blocks it. -/
def is_stable_matching {M W : Type*} (market : MarriageMarket M W)
    (μ : M ≃ W) : Prop :=
  ∀ (m : M) (w : W), ¬ is_blocking_pair market μ m w
