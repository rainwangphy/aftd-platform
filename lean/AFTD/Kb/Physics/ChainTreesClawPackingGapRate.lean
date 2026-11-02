import AFTD.Prelude

/-!
# chain_trees_claw_packing_gap_rate

Topic: quantum_mechanics   Node: a478ba581f43

Provenance: helper lemma. knowledgebase: OP-828

For every integer k ≥ 1, the gap (3k - 5k/2) / (16k) between the tripartite information bounds on the 16k-vertex chain trees is at least 1/32.
-/

/-- The asymptotic claw packing gap rate between 3k and 5k/2 on 16k vertices is at least 1/32. -/
theorem chain_trees_claw_packing_gap_rate (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / 32 ≤ ((3 * k : ℝ) - (5 * k / 2 : ℝ)) / (16 * k : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have h_eq : ((3 * k : ℝ) - (5 * k / 2 : ℝ)) / (16 * k : ℝ) = 1 / 32 := by
    field_simp
    ring
  rw [h_eq]
