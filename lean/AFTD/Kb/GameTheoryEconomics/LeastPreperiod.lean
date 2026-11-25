import AFTD.Prelude

/-!
# least_preperiod

Topic: combinatorial_games   Node: b850e83b89cc

Provenance: formalization of a published result. Source: arXiv:2611.31336

The least preperiod of a sequence s : ℕ → α with respect to a period p is the infimum of the set of natural numbers L such that s (n + p) = s n for all n ≥ L.
-/

/-- The least preperiod of a sequence with respect to a period. -/
noncomputable def least_preperiod {α : Type*} (s : ℕ → α) (p : ℕ) : ℕ := sInf {L : ℕ | ∀ n ≥ L, s (n + p) = s n}
