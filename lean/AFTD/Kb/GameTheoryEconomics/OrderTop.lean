import AFTD.Prelude

/-!
# order_top

Topic: social_choice   Node: b7f74f2ad962

Provenance: formalization of a published result. Source: arXiv:2611.26224 Sec. 2, p. 3

The top (most preferred) alternative of a linear order L on a finite nonempty set of alternatives A, defined as the maximum element under L.
-/

/-- The top-ranked alternative in a linear order on a finite nonempty set. -/
def order_top {A : Type*} [Fintype A] [Nonempty A] (L : LinearOrder A) : A := @Finset.max' A L Finset.univ Finset.univ_nonempty
