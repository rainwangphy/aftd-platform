import AFTD.Prelude
import AFTD.Kb.Tcs.MLeafyTree
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.Op1429MirrorSymmetricMLeafyTreesNOneUnique
import AFTD.Kb.Tcs.IsMLeafy
import AFTD.Kb.Tcs.PlaneTreeNumInternal
import AFTD.Kb.Tcs.PlaneTreeNumLeaves
import AFTD.Kb.Tcs.InMLeafyTrees

/-!
# op_1430_involution_group_n_one

Topic: combinatorics   Node: faa2920534e6

Provenance: helper lemma. arXiv:2611.10154 Sec. 2.1

For n = 1 and any m ≥ 1, any two involutions on MLeafyTree m 1 generate a trivial (subsingleton) permutation subgroup.
-/

/-- For n = 1, any two involutions on m-leafy trees generate a trivial permutation group. -/
theorem op_1430_involution_group_n_one (m : ℕ) (hm : 1 ≤ m)
    (τ₁ τ₂ : Equiv.Perm (MLeafyTree m 1)) (h₁ : τ₁ ^ 2 = 1) (h₂ : τ₂ ^ 2 = 1) :
    Subsingleton (Subgroup.closure {τ₁, τ₂}) := by
  haveI : Subsingleton (MLeafyTree m 1) := by
    constructor
    intro t1 t2
    apply Subtype.ext
    have h1int : plane_tree_num_internal t1.1 = 1 := t1.2.2.1
    have h2int : plane_tree_num_internal t2.1 = 1 := t2.2.2.1
    have h1leaves : plane_tree_num_leaves t1.1 = m * 1 + 1 := t1.2.2.2
    have h2leaves : plane_tree_num_leaves t2.1 = m * 1 + 1 := t2.2.2.2
    rw [op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_tree_eq_node_replicate t1.1 h1int,
        op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_tree_eq_node_replicate t2.1 h2int,
        h1leaves, h2leaves]
  infer_instance
