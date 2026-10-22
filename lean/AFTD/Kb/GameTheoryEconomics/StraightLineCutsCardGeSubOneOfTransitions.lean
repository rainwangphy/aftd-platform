import AFTD.Prelude

/-!
# straight_line_cuts_card_ge_sub_one_of_transitions

Topic: fair_division   Node: 7b0519d2f706

Provenance: helper lemma. arXiv:2610.27956 Proposition 1

If a transition count T satisfies 2(k - 1) ≤ T and T ≤ 2 * L_card, then L_card ≥ k - 1.
-/

/-- If the number of transitions along a circular necklace is at least 2(k-1) and at most 2 * |L|, then |L| ≥ k - 1. -/
theorem straight_line_cuts_card_ge_sub_one_of_transitions (k : ℕ) (T : ℕ) (L_card : ℕ)
    (h_low : 2 * (k - 1) ≤ T) (h_up : T ≤ 2 * L_card) :
    k - 1 ≤ L_card := by
  omega
