import AFTD.Prelude

/-!
# boundary_two_extra_shores_count_impossible

Topic: graphs   Node: aa3b8d0f280f

Provenance: helper lemma. OP-1957: arithmetic for two anticomplete extra shores in the nonclique four-block route.

The displayed nonnegative integer block counts, residual size, two nonempty extra-shore witnesses and defect inequalities are inconsistent.
-/

theorem boundary_two_extra_shores_count_impossible
    (k s a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 : ℕ) (hk : 5 ≤ k) (hs : 2 ≤ s)
    (hs4 : s ≤ 4) (hx : 1 ≤ a0) (hy : 1 ≤ c1)
    (htotal : a0+b0+c0+d0+a1+b1+c1+d1+a2+b2+c2+d2+a3+b3+c3+d3+s = 2*k)
    (hwsize : s ≤ a3+b3+c3+d3+1)
    (hA : a0+a1+a2+a3 ≤ 5)
    (hB : b0+b1+b2+b3+5 ≤ 2*k)
    (hC : c0+c1+c2+c3 ≤ 5)
    (hD : d0+d1+d2+d3+5 ≤ 2*k)
    (hxdef : a1+c1+d1+a2+c2+d2+a3+c3+d3 ≤ 3)
    (hydef : a0+b0+c0+a2+b2+c2+a3+b3+c3 ≤ 3)
    (hz : (1 ≤ a2 ∧ a0+c0+d0+a1+c1+d1+a3+c3+d3 ≤ 2) ∨
      (1 ≤ b2 ∧ b0+c0+d0+b1+c1+d1+b3+c3+d3+8 ≤ 2*k) ∨
      (1 ≤ c2 ∧ a0+b0+c0+a1+b1+c1+a3+b3+c3 ≤ 2) ∨
      (1 ≤ d2 ∧ a0+b0+d0+a1+b1+d1+a3+b3+d3+8 ≤ 2*k))
    (hw : (1 ≤ a3 ∧ a0+c0+d0+a1+c1+d1+a2+c2+d2 ≤ 2) ∨
      (1 ≤ b3 ∧ b0+c0+d0+b1+c1+d1+b2+c2+d2+8 ≤ 2*k) ∨
      (1 ≤ c3 ∧ a0+b0+c0+a1+b1+c1+a2+b2+c2 ≤ 2) ∨
      (1 ≤ d3 ∧ a0+b0+d0+a1+b1+d1+a2+b2+d2+8 ≤ 2*k)) : False := by
  rcases hz with hz | hz | hz | hz <;>
    rcases hw with hw | hw | hw | hw <;> omega
