import AFTD.Prelude

/-!
# poset_ramsey_property

Topic: combinatorics   Node: f342bb23b11c

Provenance: formalization of a published result. Source: arXiv:2610.20545, The k-color poset Ramsey number of the diamond is 2k

For a preordered type P and natural numbers k and d, poset_ramsey_property P k d asserts that for every coloring c : Finset (Fin d) → Fin k, there exists an order embedding f : P ↪o Finset (Fin d) and a color col : Fin k such that c (f x) = col for all x : P.
-/

/-- Predicate that every k-coloring of the Boolean lattice on Fin d contains a monochromatic induced copy of P. -/
def poset_ramsey_property (P : Type*) [Preorder P] (k d : ℕ) : Prop :=
  ∀ c : Finset (Fin d) → Fin k, ∃ f : P ↪o Finset (Fin d), ∃ col : Fin k, ∀ x : P, c (f x) = col
