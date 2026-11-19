import AFTD.Prelude

/-!
# alternating_forbidden_palettes_block_six_cycle

Topic: graphs   Node: ac8023af18f5

Provenance: helper lemma. Precolored factor-cycle obstruction for the OP-874 campaign.

Alternating complementary forbidden palettes force the three alternating factor edges into the same pair of colors, so they cannot be pairwise distinct.
-/

theorem alternating_forbidden_palettes_block_six_cycle
    (a b c d e f : Fin 4)
    (h0 : a.val < 2 ∨ f.val < 2)
    (h1 : 2 ≤ a.val ∨ 2 ≤ b.val)
    (h2 : b.val < 2 ∨ c.val < 2)
    (h3 : 2 ≤ c.val ∨ 2 ≤ d.val)
    (h4 : d.val < 2 ∨ e.val < 2)
    (h5 : 2 ≤ e.val ∨ 2 ≤ f.val)
    (hfb : f.val ≠ b.val) (hbd : b.val ≠ d.val) (hdf : d.val ≠ f.val) : False := by
  have hf : f.val < 2 ↔ b.val < 2 := by omega
  have hd : d.val < 2 ↔ b.val < 2 := by omega
  have hb := b.isLt
  have hc := d.isLt
  have he := f.isLt
  omega
