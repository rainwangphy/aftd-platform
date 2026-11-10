import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.PlaneTreeNumInternal
import AFTD.Kb.Tcs.PlaneTreeSubtrees
import AFTD.Kb.Tcs.PlaneTreeNumLeaves
import AFTD.Kb.Tcs.InMLeafyTrees
import AFTD.Kb.Tcs.PlaneTreeMirror
import AFTD.Kb.Tcs.IsMLeafy

/-!
# op_1429_mirror_symmetric_m_leafy_trees_involution

Topic: combinatorics   Node: 620c0f254797

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.3

The mirror reflection involution τ preserves the class LT_n^m of m-leafy trees with n internal vertices and mn + 1 leaves.
-/

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_induction (P : PlaneTree → Prop)
    (hleaf : P .leaf)
    (hnode : ∀ cs : List PlaneTree, (∀ c ∈ cs, P c) → P (.node cs))
    (t : PlaneTree) : P t := by
  refine PlaneTree.rec (motive_1 := P) (motive_2 := fun cs => ∀ c ∈ cs, P c)
    hleaf
    (fun cs ih => hnode cs ih)
    (by intro c hc; cases hc)
    (fun head tail ih_head ih_tail => by
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ih_head
      · exact ih_tail c hc)
    t

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_mirror_node (cs : List PlaneTree) :
    plane_tree_mirror (.node cs) = .node (cs.map plane_tree_mirror).reverse := by
  rw [plane_tree_mirror.eq_2]
  simp

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_node (cs : List PlaneTree) :
    plane_tree_num_leaves (.node cs) = (cs.map plane_tree_num_leaves).sum := by
  rw [plane_tree_num_leaves.eq_2]
  simp

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_node (cs : List PlaneTree) :
    plane_tree_num_internal (.node cs) = 1 + (cs.map plane_tree_num_internal).sum := by
  rw [plane_tree_num_internal.eq_2]
  simp

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_subtrees_node (cs : List PlaneTree) :
    plane_tree_subtrees (.node cs) = .node cs :: cs.flatMap plane_tree_subtrees := by
  rw [plane_tree_subtrees.eq_2]
  simp

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_mirror (t : PlaneTree) :
    plane_tree_num_leaves (plane_tree_mirror t) = plane_tree_num_leaves t := by
  induction t using op_1429_mirror_symmetric_m_leafy_trees_involution_induction with
  | hleaf =>
    rw [plane_tree_mirror.eq_1]
  | hnode cs ih =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_mirror_node,
        op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_node,
        op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_node]
    rw [List.map_reverse, List.sum_reverse]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact ih x hx

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_mirror (t : PlaneTree) :
    plane_tree_num_internal (plane_tree_mirror t) = plane_tree_num_internal t := by
  induction t using op_1429_mirror_symmetric_m_leafy_trees_involution_induction with
  | hleaf =>
    rw [plane_tree_mirror.eq_1]
  | hnode cs ih =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_mirror_node,
        op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_node,
        op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_node]
    rw [List.map_reverse, List.sum_reverse]
    congr 2
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact ih x hx

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_mem_subtrees_mirror (t : PlaneTree) (s : PlaneTree)
    (hs : s ∈ plane_tree_subtrees (plane_tree_mirror t)) :
    ∃ u ∈ plane_tree_subtrees t, s = plane_tree_mirror u := by
  induction t using op_1429_mirror_symmetric_m_leafy_trees_involution_induction generalizing s with
  | hleaf =>
    rw [plane_tree_mirror.eq_1, plane_tree_subtrees.eq_1] at hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact ⟨.leaf, by rw [plane_tree_subtrees.eq_1]; simp, plane_tree_mirror.eq_1.symm⟩
  | hnode cs ih =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_mirror_node,
        op_1429_mirror_symmetric_m_leafy_trees_involution_subtrees_node] at hs
    simp only [List.mem_cons, List.mem_flatMap] at hs
    rcases hs with rfl | ⟨c', hc', hs⟩
    · exact ⟨.node cs, by rw [op_1429_mirror_symmetric_m_leafy_trees_involution_subtrees_node]; simp,
             by rw [op_1429_mirror_symmetric_m_leafy_trees_involution_mirror_node]⟩
    · rw [List.mem_reverse, List.mem_map] at hc'
      rcases hc' with ⟨c, hc, rfl⟩
      rcases ih c hc s hs with ⟨u, hu, rfl⟩
      refine ⟨u, ?_, rfl⟩
      rw [op_1429_mirror_symmetric_m_leafy_trees_involution_subtrees_node]
      simp only [List.mem_cons, List.mem_flatMap]
      right
      exact ⟨c, hc, hu⟩

theorem op_1429_mirror_symmetric_m_leafy_trees_involution_is_m_leafy_mirror (m : ℕ) (t : PlaneTree)
    (h : is_m_leafy m t) :
    is_m_leafy m (plane_tree_mirror t) := by
  intro s hs
  rcases op_1429_mirror_symmetric_m_leafy_trees_involution_mem_subtrees_mirror t s hs with ⟨u, hu, rfl⟩
  rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_mirror,
      op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_mirror]
  exact h u hu

/-- The mirror reflection map preserves membership in LT_n^m. -/
theorem op_1429_mirror_symmetric_m_leafy_trees_involution (m n : ℕ) (t : PlaneTree)
    (h : in_m_leafy_trees m n t) :
    in_m_leafy_trees m n (plane_tree_mirror t) := by
  rcases h with ⟨hlef, hint, hlea⟩
  refine ⟨op_1429_mirror_symmetric_m_leafy_trees_involution_is_m_leafy_mirror m t hlef, ?_, ?_⟩
  · rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_mirror, hint]
  · rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_mirror, hlea]
