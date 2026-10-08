import AFTD.Prelude

/-!
# is_single_peaked

Topic: social_choice   Node: 3c85cd0407de

Provenance: formalization of a published result. Source: Black (1948), The Decisions of a Committee Using a Special Majority; Arrow (1951)

A strict preference relation P over a linearly ordered set of alternatives A is single-peaked with peak p if moving toward p strictly increases preference: for x < y ≤ p or p ≤ y < x, y is strictly preferred to x.
-/

/-- Single-peakedness of a pairwise strict preference relation along a linear order of alternatives. -/
def is_single_peaked {A : Type*} [LinearOrder A] (P : A → A → Prop) (p : A) : Prop := ∀ x y : A, ((x < y ∧ y ≤ p) ∨ (p ≤ y ∧ y < x)) → P y x
