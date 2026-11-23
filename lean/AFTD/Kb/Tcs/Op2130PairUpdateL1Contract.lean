import AFTD.Prelude

/-!
# op_2130_pair_update_l1_contract

Topic: online_algorithms   Node: c1a22705e605

Provenance: helper lemma. OP-2130, synchronous greedy coupling

Two greedy updates using the same tie coin do not increase the sum of the absolute differences between the two pairs, provided corresponding discrepancies have the same parity.
-/

theorem op_2130_pair_update_l1_contract (a b x y : ℤ) (c : Bool) (ha : a % 2 = x % 2) (hb : b % 2 = y % 2) : let p : ℤ := if a < b then 1 else if b < a then -1 else if c then 1 else -1; let q : ℤ := if x < y then 1 else if y < x then -1 else if c then 1 else -1; |(a + p) - (x + q)| + |(b - p) - (y - q)| ≤ |a - x| + |b - y| := by
  dsimp only
  split_ifs <;> simp only [abs, max_def] <;> split_ifs <;> omega
