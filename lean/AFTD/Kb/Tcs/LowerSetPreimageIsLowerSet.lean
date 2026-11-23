import AFTD.Prelude

/-!
# lowerSet_preimage_isLowerSet

Topic: combinatorics   Node: c2e781343884

Provenance: formalization of a published result. Source: arXiv:2611.26888 Proposition 3.2

If I is an order ideal of a poset P and f is a poset automorphism of P, then the preimage f⁻¹(I) is an order ideal of P.
-/

/-- The preimage of an order ideal under a poset automorphism is an order ideal. -/
theorem lowerSet_preimage_isLowerSet {P : Type*} [PartialOrder P]
    (f : P ≃o P) (I : LowerSet P) :
    IsLowerSet (f ⁻¹' (I : Set P)) :=
  I.lower'.preimage f.monotone
