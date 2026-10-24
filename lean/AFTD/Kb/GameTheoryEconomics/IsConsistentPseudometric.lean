import AFTD.Prelude

/-!
# is_consistent_pseudometric

Topic: social_choice   Node: eef677b48701

Provenance: formalization of a published result. Source: arXiv:2610.26535 Section 2.1

Given types V and C, a pseudometric space instance on V ⊕ C, and an election profile prof : V → LinearOrder C assigning a linear order on C to each voter v in V, is_consistent_pseudometric V C prof asserts that for all voters v in V and all candidates a and b in C, if dist (Sum.inl v) (Sum.inr a) < dist (Sum.inl v) (Sum.inr b), then (prof v).lt b a (meaning candidate b is strictly less than candidate a under the linear order prof v).
-/

/-- Consistency between a pseudometric space on V ⊕ C and an election profile. -/
def is_consistent_pseudometric (V C : Type*) [PseudoMetricSpace (V ⊕ C)]
    (prof : V → LinearOrder C) : Prop :=
  ∀ (v : V) (a b : C),
    dist (Sum.inl v) (Sum.inr a) < dist (Sum.inl v) (Sum.inr b) →
      (prof v).lt b a
