import AFTD.Prelude

/-!
# is_poset_linear_extension

Topic: combinatorics   Node: 2d9b2a51b1e2

Provenance: formalization of a published result. Source: arXiv:2611.26888 Section 2.1

A function l from a finite partially ordered set P to Fin |P| is a linear extension if it is bijective and order-preserving.
-/

/-- A linear extension of a finite poset P is a bijective order-preserving map to Fin |P|. -/
def is_poset_linear_extension {P : Type*} [PartialOrder P] [Fintype P]
    (l : P → Fin (Fintype.card P)) : Prop := Function.Bijective l ∧ ∀ ⦃x y : P⦄, x ≤ y → l x ≤ l y
