import AFTD.Prelude

/-!
# satisfies_objectwise_mm

Topic: fair_division   Node: d775a3e5a8d7

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 4.2

Given types Agent and Object, a rule f : (Agent -> LinearOrder Object) -> Agent -> Finset Object satisfies satisfies_objectwise_mm if for all preference profiles succ and succ' of type Agent -> LinearOrder Object, whenever for every agent i, every object y ∈ f succ i, and every object z : Object, (succ i).lt z y implies (succ' i).lt z y, then f succ' = f succ.
-/

/-- A rule satisfies object-wise Maskin monotonicity if expanding lower contour sets preserves allocations. -/
def satisfies_objectwise_mm {Agent Object : Type*}
    (f : (Agent → LinearOrder Object) → Agent → Finset Object) : Prop :=
  ∀ (succ succ' : Agent → LinearOrder Object),
    (∀ i, ∀ y ∈ f succ i, ∀ z : Object, (succ i).lt z y → (succ' i).lt z y) →
    f succ' = f succ
