import AFTD.Prelude
import AFTD.Kb.Tcs.IntFourSubAbsLeAbs

/-!
# path_radio_label_four_mul_add_three_sep

Topic: graphs   Node: 0be3f00fc650

Provenance: helper lemma. for simple_graph_path_radio_labeling_four_mul_add_three (RT-4, OP-384)

The labels of the explicit labeling of P_{4m+3} (odd x: x + 4a; even x: 2((x/2) mod 2) + 4a, plus 4m when a >= x/4) at vertices x, y with indices a, b (distinct if x = y) differ by at least 4 - |x - y|.
-/

set_option maxHeartbeats 4000000 in
theorem path_radio_label_four_mul_add_three_sep (m x y a b : ℕ) (hx : x < 4 * m + 3)
    (hy : y < 4 * m + 3) (ha : a < m) (hb : b < m) (hne : x ≠ y ∨ a ≠ b) :
    (4 : ℤ) - |(x : ℤ) - y| ≤
      |(((if x % 2 = 1 then x + 4 * a else 2 * (x / 2 % 2) + 4 * a + if a < x / 4 then 0 else 4 * m) :
          ℕ) : ℤ) -
        (((if y % 2 = 1 then y + 4 * b else 2 * (y / 2 % 2) + 4 * b + if b < y / 4 then 0 else 4 * m) :
          ℕ) : ℤ)| := by
  apply int_four_sub_abs_le_abs <;> intro hs <;> split_ifs <;> push_cast <;> omega
