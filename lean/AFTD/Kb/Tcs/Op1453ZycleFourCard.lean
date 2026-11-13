import AFTD.Prelude
import AFTD.Kb.Tcs.Zycle

/-!
# op_1453_zycle_four_card

Topic: combinatorics   Node: badc7bea5b62

Provenance: formalization of a published result. Source: arXiv:2611.12582 Section 1

The 4-zycle Z₄ has exactly 8 hyperedges.
-/

/-- The 4-zycle Z₄ has 8 edges. -/
theorem op_1453_zycle_four_card : (zycle 4).card = 8 := rfl
