import AFTD.Prelude
import AFTD.Kb.Tcs.StandardCoreTwoOne

/-!
# standard_core_two_one_card

Topic: graphs   Node: 6200cf482498

Provenance: helper lemma. arXiv:2611.18633 Theorem 4.3

The cardinality of standard_core_two_one is equal to 12.
-/

/-- The canonical 4 × 4 square with corners removed has 12 points. -/
theorem standard_core_two_one_card : standard_core_two_one.card = 12 := rfl
