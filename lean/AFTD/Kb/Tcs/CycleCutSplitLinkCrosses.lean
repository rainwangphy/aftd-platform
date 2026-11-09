import AFTD.Prelude

/-!
# cycle_cut_split_link_crosses

Topic: online_algorithms   Node: a297fdffa56f

Provenance: helper lemma. arXiv:2611.08570, Theorem 5.4

For integers i, j, a, b, m satisfying a ≤ m < b, if candidate link (i, j) crosses cycle cut [a, b] (meaning (a ≤ i ∧ i ≤ b) ↔ ¬(a ≤ j ∧ j ≤ b)), then it crosses exactly one of the two sub-cuts [a, m] and [m + 1, b].
-/

/-- A link crossing cut [a, b] crosses exactly one of the halves [a, m] or [m + 1, b]. -/
theorem cycle_cut_split_link_crosses (i j a b m : ℤ)
    (h_ab : a ≤ m ∧ m < b)
    (h_cross : (a ≤ i ∧ i ≤ b) ↔ ¬(a ≤ j ∧ j ≤ b)) :
    (((a ≤ i ∧ i ≤ m) ↔ ¬(a ≤ j ∧ j ≤ m)) ∨
     ((m + 1 ≤ i ∧ i ≤ b) ↔ ¬(m + 1 ≤ j ∧ j ≤ b))) ∧
    ¬ (((a ≤ i ∧ i ≤ m) ↔ ¬(a ≤ j ∧ j ≤ m)) ∧
       ((m + 1 ≤ i ∧ i ≤ b) ↔ ¬(m + 1 ≤ j ∧ j ≤ b))) := by
  omega
