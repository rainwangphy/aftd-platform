import AFTD.Prelude

/-!
# cycle_link_crosses_cut_iff_tl_rect

Topic: online_algorithms   Node: 7e9dfeec8bf9

Provenance: formalization of a published result. Source: arXiv:2611.08570 Proposition 3.2

For integers i, j, a, b, n satisfying 0 ≤ i < j < n and 1 ≤ a ≤ b < n, candidate link (i, j) crosses cycle cut [a, b] (meaning (a ≤ i ∧ i ≤ b) ↔ ¬(a ≤ j ∧ j ≤ b)) if and only if (i, j) lies in the union of the leftless rectangle (i ≤ a - 1 ∧ a ≤ j ≤ b) and the topless rectangle (a ≤ i ≤ b ∧ b + 1 ≤ j).
-/

/-- Proposition 3.2: A candidate link crosses cycle cut [a, b] if and only if it belongs to the TL-rectangle shape. -/
theorem cycle_link_crosses_cut_iff_tl_rect (i j a b n : ℤ)
    (h_ij : 0 ≤ i ∧ i < j ∧ j < n) (h_ab : 1 ≤ a ∧ a ≤ b ∧ b < n) :
    ((a ≤ i ∧ i ≤ b) ↔ ¬(a ≤ j ∧ j ≤ b)) ↔
      ((i ≤ a - 1 ∧ a ≤ j ∧ j ≤ b) ∨ (a ≤ i ∧ i ≤ b ∧ b + 1 ≤ j)) := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
