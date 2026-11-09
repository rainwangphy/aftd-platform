import AFTD.Prelude

/-!
# is_allocation_rule

Topic: fair_division   Node: b0bec108a2f0

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 2.3

Given types Agent and Object, a rule f : (Agent -> LinearOrder Object) -> Agent -> Finset Object satisfies is_allocation_rule if for every preference profile succ : Agent -> LinearOrder Object and all distinct agents i ≠ j, the finite bundles f succ i and f succ j of type Finset Object are disjoint.
-/

/-- A rule maps preference profiles to allocations if bundles of distinct agents are disjoint. -/
def is_allocation_rule {Agent Object : Type*}
    (f : (Agent → LinearOrder Object) → Agent → Finset Object) : Prop :=
  ∀ succ i j, i ≠ j → Disjoint (f succ i) (f succ j)
