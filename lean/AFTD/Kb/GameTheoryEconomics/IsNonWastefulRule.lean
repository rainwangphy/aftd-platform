import AFTD.Prelude

/-!
# is_non_wasteful_rule

Topic: fair_division   Node: 2a69ec429b45

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 2.3

Given finite types Agent and Object with decidable equality on Object, a rule f : (Agent -> LinearOrder Object) -> Agent -> Finset Object satisfies is_non_wasteful_rule if for every preference profile succ : Agent -> LinearOrder Object, the union over all agents of the finite bundles f succ a equals the universe of objects Finset.univ.
-/

/-- A rule is non-wasteful if all objects are allocated at every profile. -/
def is_non_wasteful_rule {Agent Object : Type*} [Fintype Agent] [Fintype Object] [DecidableEq Object]
    (f : (Agent → LinearOrder Object) → Agent → Finset Object) : Prop :=
  ∀ succ, Finset.univ.biUnion (f succ) = Finset.univ
