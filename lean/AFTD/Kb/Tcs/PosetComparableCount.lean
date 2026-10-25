import AFTD.Prelude

/-!
# poset_comparable_count

Topic: combinatorics   Node: 9619b4edeac8

Provenance: helper lemma. step towards poset_height_one_reconstructible_of_no_isolated

The number of points of P comparable with x (the 'degree' of x: for a height-one poset without isolated points this is the degree of x in the associated bipartite graph whose edges are the comparable pairs).
-/

/-- The number of points comparable with a given point (its 'degree'). -/
noncomputable def poset_comparable_count (P : Type*) [PartialOrder P] (x : P) : Nat := Nat.card {y : P // y < x ∨ x < y}
