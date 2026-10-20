import AFTD.Prelude

/-!
# poset_lt_pair_count

Topic: combinatorics   Node: 157cac49bdeb

Provenance: helper lemma. step towards poset_height_one_reconstructible

The number of comparable pairs (ordered pairs a < b) of an ordered set, as a natural number.
-/

/-- The number of strict-comparable ordered pairs of an ordered set. -/
noncomputable def poset_lt_pair_count (P : Type*) [PartialOrder P] : Nat := Nat.card {p : P × P // p.1 < p.2}
