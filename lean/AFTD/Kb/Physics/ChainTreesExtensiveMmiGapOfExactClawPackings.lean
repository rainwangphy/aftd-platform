import AFTD.Prelude
import AFTD.Kb.Physics.ChainTreesFloorClawPackingGapGe
import AFTD.Kb.Physics.MaxClawPacking
import AFTD.Kb.Physics.ChainTree1
import AFTD.Kb.Physics.ChainTree2

/-!
# chain_trees_extensive_mmi_gap_of_exact_claw_packings

Topic: quantum_mechanics   Node: deb73cbd2d0d

Provenance: helper lemma. arXiv:2511.19585

For any integer k ≥ 1, if max_claw_packing (chain_tree_1 k) = 5 * k / 2 in ℕ (using integer division) and max_claw_packing (chain_tree_2 k) = 3 * k in ℕ, then ((max_claw_packing (chain_tree_2 k) : ℝ) - (max_claw_packing (chain_tree_1 k) : ℝ)) / (16 * k : ℝ) ≥ 1 / 32.
-/

/-- If the chain trees achieve claw packings 5k/2 and 3k in Nat, their normalized gap is at least 1/32. -/
theorem chain_trees_extensive_mmi_gap_of_exact_claw_packings (k : ℕ) (hk : 1 ≤ k)
    (h1 : max_claw_packing (chain_tree_1 k) = 5 * k / 2)
    (h2 : max_claw_packing (chain_tree_2 k) = 3 * k) :
    (1 : ℝ) / 32 ≤ ((max_claw_packing (chain_tree_2 k) : ℝ) - (max_claw_packing (chain_tree_1 k) : ℝ)) / (16 * k : ℝ) := by
  rw [h1, h2]
  exact chain_trees_floor_claw_packing_gap_ge k hk
