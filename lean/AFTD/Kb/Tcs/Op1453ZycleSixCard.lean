import AFTD.Prelude
import AFTD.Kb.Tcs.Zycle

/-!
# op_1453_zycle_six_card

Topic: combinatorics   Node: 80fb067c3489

Provenance: formalization of a published result. Source: arXiv:2611.12582 Section 1

The 6-zycle Z₆ has exactly 12 hyperedges.
-/

/-- The 6-zycle Z₆ has 12 edges. -/
theorem op_1453_zycle_six_card : (zycle 6).card = 12 := rfl
