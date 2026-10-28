import AFTD.Prelude

/-!
# odd_div_two_cancel_le

Topic: graphs   Node: 4cf3e07363e3

Provenance: helper lemma. step towards complete_graph_odd_line_graph_le_chromaticNumber

For odd n ≥ 3, if n * (n - 1) / 2 ≤ m * ((n - 1) / 2), then n ≤ m.
-/

/-- For odd n ≥ 3, cancellation of (n - 1) / 2 preserves inequality. -/
theorem odd_div_two_cancel_le (n m : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) (h : n * (n - 1) / 2 ≤ m * ((n - 1) / 2)) : n ≤ m := by
  have hdvd : 2 ∣ (n - 1) := ⟨n / 2, by omega⟩
  rw [Nat.mul_div_assoc _ hdvd] at h
  have hpos : 0 < (n - 1) / 2 := by omega
  exact Nat.le_of_mul_le_mul_right h hpos
