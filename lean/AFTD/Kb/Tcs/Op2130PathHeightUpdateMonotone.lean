import AFTD.Prelude

/-!
# op_2130_path_height_update_monotone

Topic: online_algorithms   Node: ebf1cef4291f

Provenance: helper lemma. OP-2130: attractive coupling for cumulative path discrepancies

A single cumulative-height update preserves coordinatewise order when the center heights have the same parity and the two tie-breaking coins are ordered.
-/

theorem op_2130_path_height_update_monotone (l m r L M R : ℤ) (coin coin' : Bool) (hl : l ≤ L) (hm : m ≤ M) (hr : r ≤ R) (hp : m % 2 = M % 2) (hc : coin = false ∨ coin' = true) : m + (if 2 * m < l + r then 1 else if l + r < 2 * m then -1 else if coin then 1 else -1) ≤ M + (if 2 * M < L + R then 1 else if L + R < 2 * M then -1 else if coin' then 1 else -1) := by
  cases coin <;> cases coin' <;> simp_all <;> split_ifs <;> omega
