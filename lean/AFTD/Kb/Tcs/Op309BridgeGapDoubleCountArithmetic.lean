import AFTD.Prelude

/-!
# op309_bridge_gap_double_count_arithmetic

Topic: graphs   Node: d7ac549e35d4

Provenance: helper lemma. OP-309 bridge-tree gap counting argument.

Charging good blocks injectively to covered connectors gives the total uncovered-vertex upper bound.
-/

theorem op309_bridge_gap_double_count_arithmetic
  (k h good blockU hubU total : ℕ) (hh : h + 2 = k)
  (hblock : blockU ≤ k + good) (hcovered : hubU + good ≤ h)
  (htotal : total = blockU + hubU) : total + 2 ≤ 2 * k := by omega
