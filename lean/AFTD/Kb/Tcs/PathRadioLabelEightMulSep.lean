import AFTD.Prelude
import AFTD.Kb.Tcs.IntFourSubAbsLeAbs

/-!
# path_radio_label_eight_mul_sep

Topic: graphs   Node: b7a7d96102c9

Provenance: helper lemma. for simple_graph_multi_radio_number_path_le_eight_mul (arXiv:2610.25863 Proposition 4.4)

The labels 8a + (3x mod 8) and 8b + (3y mod 8) (with x ≠ y or a ≠ b) differ by at least 4 - |x - y|.
-/

set_option maxHeartbeats 2000000 in
theorem path_radio_label_eight_mul_sep (x y a b : ℕ) (hne : x ≠ y ∨ a ≠ b) :
    (4 : ℤ) - |(x : ℤ) - y| ≤ |(((8 * a + 3 * x % 8 : ℕ)) : ℤ) - ((8 * b + 3 * y % 8 : ℕ) : ℤ)| := by
  rcases (show (x : ℤ) - y ≤ -4 ∨ (x : ℤ) - y = -3 ∨ (x : ℤ) - y = -2 ∨ (x : ℤ) - y = -1 ∨
      (x : ℤ) - y = 0 ∨ (x : ℤ) - y = 1 ∨ (x : ℤ) - y = 2 ∨ (x : ℤ) - y = 3 ∨ 4 ≤ (x : ℤ) - y by
        omega) with h | h | h | h | h | h | h | h | h <;>
    apply int_four_sub_abs_le_abs <;> intro hs <;> push_cast <;> omega
