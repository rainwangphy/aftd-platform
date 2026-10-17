import AFTD.Prelude
import AFTD.Kb.Tcs.MixedCageOrder
import AFTD.Kb.Tcs.MixedCageOrderGirthThree

/-!
# mixed_cage_order_one_girth_three

Topic: graphs   Node: 64d3a85b5dbe

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Theorem 5.1 with r = 1 (the case g = 3 of Conjecture 2).

The case g = 3 of the conjecture: n(1, z, 3) = N(z, 3), i.e. 2z + 2 for every z ≥ 1 (both parities agree).
-/

theorem mixed_cage_order_one_girth_three (z : ℕ) (hz : 1 ≤ z) :
    mixed_cage_order 1 z 3 = if Even z then z * (3 - 1) + 2 else (z + 1) * (3 - 1) := by
  rw [mixed_cage_order_girth_three 1 z le_rfl hz]
  split_ifs <;> omega
