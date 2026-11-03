import AFTD.Prelude
import AFTD.Kb.Physics.ChainTreesClawPackingGapRate

/-!
# chain_trees_floor_claw_packing_gap_ge

Topic: quantum_mechanics   Node: c60fed71d8be

Provenance: helper lemma. arXiv:2511.19585

For every integer k ≥ 1, the normalized gap (3k - ⌊5k/2⌋) / (16k) between the integer tripartite information bounds on the 16k-vertex chain trees is at least 1/32.
-/

/-- The normalized difference between 3k and the integer floor 5k/2 is at least 1/32. -/
theorem chain_trees_floor_claw_packing_gap_ge (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / 32 ≤ (((3 * k : ℕ) : ℝ) - ((5 * k / 2 : ℕ) : ℝ)) / (16 * k : ℝ) := by
  have h1 : (1 : ℝ) / 32 ≤ ((3 * k : ℝ) - (5 * k / 2 : ℝ)) / (16 * k : ℝ) :=
    chain_trees_claw_packing_gap_rate k hk
  have h_div : ((5 * k / 2 : ℕ) : ℝ) ≤ ((5 * k : ℕ) : ℝ) / 2 := Nat.cast_div_le
  have h_num : ((3 * k : ℝ) - (5 * k / 2 : ℝ)) ≤ (((3 * k : ℕ) : ℝ) - ((5 * k / 2 : ℕ) : ℝ)) := by
    push_cast at h_div ⊢
    linarith
  have h_denom : 0 ≤ (16 * k : ℝ) := by positivity
  have h2 : ((3 * k : ℝ) - (5 * k / 2 : ℝ)) / (16 * k : ℝ) ≤
      (((3 * k : ℕ) : ℝ) - ((5 * k / 2 : ℕ) : ℝ)) / (16 * k : ℝ) :=
    div_le_div_of_nonneg_right h_num h_denom
  exact le_trans h1 h2
