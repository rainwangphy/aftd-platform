import AFTD.Prelude

/-!
# low_hole_reduction_forces_zero

Topic: combinatorics   Node: d7362c5ceb9f

Provenance: helper lemma. scout/2610-22875-overtake-and-the-recursive-line-equality-for-second-order-z.md:553

For integers L, h, H, and d, if 0 ≤ H, 0 ≤ d, L = h - H - d, 2 ≤ L, and h ≤ 2, then h = 2 ∧ H = 0 ∧ d = 0.
-/

/-- If non-negative integers H and d satisfy L = h - H - d with 2 ≤ L and h ≤ 2, then h = 2, H = 0, and d = 0. -/
theorem low_hole_reduction_forces_zero (L h H d : ℤ)
    (hH : 0 ≤ H) (hd : 0 ≤ d)
    (hid : L = h - H - d)
    (hL : 2 ≤ L) (hh : h ≤ 2) :
    h = 2 ∧ H = 0 ∧ d = 0 := by
  omega
