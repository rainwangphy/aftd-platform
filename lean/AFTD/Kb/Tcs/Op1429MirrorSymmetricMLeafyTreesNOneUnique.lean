import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTreeNumInternal
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.Op1429MirrorSymmetricMLeafyTreesNonempty
import AFTD.Kb.Tcs.IsMLeafy
import AFTD.Kb.Tcs.PlaneTreeNumLeaves
import AFTD.Kb.Tcs.Op1429MirrorSymmetricMLeafyTreesInvolution
import AFTD.Kb.Tcs.MirrorSymmetricMLeafyTrees
import AFTD.Kb.Tcs.PlaneTreeMirror
import AFTD.Kb.Tcs.InMLeafyTrees

/-!
# op_1429_mirror_symmetric_m_leafy_trees_n_one_unique

Topic: combinatorics   Node: b2a1d006d1d5

Provenance: helper lemma. arXiv:2611.10154 Sec. 2.3

For every natural number m ≥ 1, there exists a unique tree t such that t ∈ mirror_symmetric_m_leafy_trees m 1.
-/

lemma op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_num_internal_eq_zero (t : PlaneTree)
    (h : plane_tree_num_internal t = 0) :
    t = PlaneTree.leaf := by
  cases t with
  | leaf => rfl
  | node cs =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_node] at h
    omega

lemma op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_list_eq_replicate_leaf (cs : List PlaneTree)
    (h : ∀ c ∈ cs, c = PlaneTree.leaf) :
    cs = List.replicate cs.length PlaneTree.leaf := by
  induction cs with
  | nil => rfl
  | cons head tail ih =>
    have hhead : head = PlaneTree.leaf := h head List.mem_cons_self
    have htail : ∀ c ∈ tail, c = PlaneTree.leaf := fun c hc => h c (List.mem_cons_of_mem head hc)
    rw [hhead, List.length_cons, List.replicate_succ]
    congr 1
    exact ih htail

lemma op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_list_leaves_sum (cs : List PlaneTree)
    (h : ∀ c ∈ cs, c = PlaneTree.leaf) :
    (List.map plane_tree_num_leaves cs).sum = cs.length := by
  induction cs with
  | nil => rfl
  | cons head tail ih =>
    have hhead : head = PlaneTree.leaf := h head List.mem_cons_self
    have htail : ∀ c ∈ tail, c = PlaneTree.leaf := fun c hc => h c (List.mem_cons_of_mem head hc)
    rw [List.map_cons, List.sum_cons, hhead, plane_tree_num_leaves.eq_1, ih htail, List.length_cons]
    omega

lemma op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_nat_list_sum_eq_zero (l : List ℕ)
    (h : l.sum = 0) (x : ℕ) (hx : x ∈ l) : x = 0 := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.sum_cons] at h
    have : head = 0 ∧ tail.sum = 0 := by omega
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact this.1
    · exact ih this.2 hmem

lemma op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_tree_eq_node_replicate (t : PlaneTree)
    (hint : plane_tree_num_internal t = 1) :
    t = PlaneTree.node (List.replicate (plane_tree_num_leaves t) PlaneTree.leaf) := by
  cases t with
  | leaf =>
    rw [plane_tree_num_internal.eq_1] at hint
    contradiction
  | node cs =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_node] at hint
    have hsum : (List.map plane_tree_num_internal cs).sum = 0 := by omega
    have hcs_zero : ∀ c ∈ cs, plane_tree_num_internal c = 0 := by
      intro c hc
      have hmem : plane_tree_num_internal c ∈ List.map plane_tree_num_internal cs :=
        List.mem_map_of_mem hc
      exact op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_nat_list_sum_eq_zero _ hsum _ hmem
    have hcs_leaf : ∀ c ∈ cs, c = PlaneTree.leaf := fun c hc =>
      op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_num_internal_eq_zero c (hcs_zero c hc)
    have hcs_eq : cs = List.replicate cs.length PlaneTree.leaf :=
      op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_list_eq_replicate_leaf cs hcs_leaf
    have hleaves : plane_tree_num_leaves (PlaneTree.node cs) = cs.length := by
      rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_node]
      exact op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_list_leaves_sum cs hcs_leaf
    rw [hleaves]
    congr 1

/-- For n = 1 and any m ≥ 1, there exists a unique tree in mirror_symmetric_m_leafy_trees m 1. -/
theorem op_1429_mirror_symmetric_m_leafy_trees_n_one_unique (m : ℕ) (hm : 1 ≤ m) :
    ∃! t : PlaneTree, t ∈ mirror_symmetric_m_leafy_trees m 1 := by
  rcases op_1429_mirror_symmetric_m_leafy_trees_nonempty m 1 hm le_rfl with ⟨t0, ht0⟩
  refine ⟨t0, ht0, fun y hy => ?_⟩
  have h_eq : ∀ t, t ∈ mirror_symmetric_m_leafy_trees m 1 →
      t = PlaneTree.node (List.replicate (m + 1) PlaneTree.leaf) := by
    intro t ht
    rcases ht with ⟨⟨-, hint, hleaves⟩, -⟩
    have ht_shape := op_1429_mirror_symmetric_m_leafy_trees_n_one_unique_tree_eq_node_replicate t hint
    rw [hleaves] at ht_shape
    have : m * 1 + 1 = m + 1 := by omega
    rw [this] at ht_shape
    exact ht_shape
  rw [h_eq y hy, h_eq t0 ht0]
