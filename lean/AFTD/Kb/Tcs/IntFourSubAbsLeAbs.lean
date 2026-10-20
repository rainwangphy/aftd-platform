import AFTD.Prelude

/-!
# int_four_sub_abs_le_abs

Topic: graphs   Node: 834143da2b76

Provenance: helper lemma. for simple_graph_path_radio_labeling_four_mul_add_three (RT-4, OP-384)

For integers d, e: if e >= 4 - d or e <= d - 4 when d >= 0, and e >= 4 + d or e <= -4 - d when d < 0, then 4 - |d| <= |e|.
-/

theorem int_four_sub_abs_le_abs {d e : ℤ} (h1 : 0 ≤ d → (4 - d ≤ e ∨ e ≤ d - 4))
    (h2 : d < 0 → (4 + d ≤ e ∨ e ≤ -4 - d)) : 4 - |d| ≤ |e| := by
  rcases abs_cases d with ⟨e1, hd⟩ | ⟨e1, hd⟩ <;> rcases abs_cases e with ⟨e2, he⟩ | ⟨e2, he⟩ <;>
    rw [e1, e2] <;> [have := h1 hd; have := h1 hd; have := h2 hd; have := h2 hd] <;> omega
