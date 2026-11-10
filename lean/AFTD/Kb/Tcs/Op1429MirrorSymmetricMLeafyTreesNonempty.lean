import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTreeNumInternal
import AFTD.Kb.Tcs.Op1429MirrorSymmetricMLeafyTreesInvolution
import AFTD.Kb.Tcs.PlaneTreeSubtrees
import AFTD.Kb.Tcs.PlaneTreeMirror
import AFTD.Kb.Tcs.IsMLeafy
import AFTD.Kb.Tcs.PlaneTreeNumLeaves
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.MirrorSymmetricMLeafyTrees
import AFTD.Kb.Tcs.InMLeafyTrees

/-!
# op_1429_mirror_symmetric_m_leafy_trees_nonempty

Topic: combinatorics   Node: b9fe65cde890

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.3

For all natural numbers m ≥ 1 and n ≥ 1, the set mirror_symmetric_m_leafy_trees m n is nonempty.
-/

def op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain (k : ℕ) : ℕ → PlaneTree
  | 0 => PlaneTree.node (List.replicate k PlaneTree.leaf)
  | j + 1 => PlaneTree.node [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain k j]

theorem op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_num_internal (k j : ℕ) :
    plane_tree_num_internal (op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain k j) = j + 1 := by
  induction j with
  | zero =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain]
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_node]
    have h : List.map plane_tree_num_internal (List.replicate k PlaneTree.leaf) = List.replicate k 0 := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, plane_tree_num_internal.eq_1, ih]
    rw [h]
    simp
  | succ j ih =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain]
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_internal_node]
    simp [ih]
    omega

theorem op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_num_leaves (k j : ℕ) :
    plane_tree_num_leaves (op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain k j) = k := by
  induction j with
  | zero =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain]
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_node]
    have h : List.map plane_tree_num_leaves (List.replicate k PlaneTree.leaf) = List.replicate k 1 := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, plane_tree_num_leaves.eq_1, ih]
    rw [h]
    simp
  | succ j ih =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain]
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_num_leaves_node]
    simp [ih]

theorem op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_mirror (k j : ℕ) :
    plane_tree_mirror (op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain k j) =
      op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain k j := by
  induction j with
  | zero =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain]
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_mirror_node]
    have h : List.map plane_tree_mirror (List.replicate k PlaneTree.leaf) = List.replicate k PlaneTree.leaf := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, plane_tree_mirror.eq_1, ih]
    rw [h]
    simp
  | succ j ih =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain]
    rw [op_1429_mirror_symmetric_m_leafy_trees_involution_mirror_node]
    simp [ih]

theorem op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_subtrees_mem (k j : ℕ) {s : PlaneTree}
    (hs : s ∈ plane_tree_subtrees (op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain k j)) :
    s = PlaneTree.leaf ∨ ∃ i ≤ j, s = op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain k i := by
  induction j with
  | zero =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain, op_1429_mirror_symmetric_m_leafy_trees_involution_subtrees_node] at hs
    simp only [List.mem_cons] at hs
    rcases hs with h | h
    · right; exact ⟨0, le_refl 0, h⟩
    · left
      have hsub : ∀ x ∈ List.flatMap plane_tree_subtrees (List.replicate k PlaneTree.leaf), x = PlaneTree.leaf := by
        intro x hx
        rw [List.mem_flatMap] at hx
        rcases hx with ⟨c, hc, hxc⟩
        have hcleaf : c = PlaneTree.leaf := List.eq_of_mem_replicate hc
        subst hcleaf
        rw [plane_tree_subtrees.eq_1] at hxc
        simp only [List.mem_singleton] at hxc
        exact hxc
      exact hsub s h
  | succ j ih =>
    rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain, op_1429_mirror_symmetric_m_leafy_trees_involution_subtrees_node] at hs
    simp only [List.mem_cons] at hs
    rcases hs with h | h
    · right; exact ⟨j + 1, le_refl _, h⟩
    · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
      rcases ih h with hleaf | ⟨i, hle, heq⟩
      · left; exact hleaf
      · right; exact ⟨i, Nat.le_succ_of_le hle, heq⟩

theorem op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_is_m_leafy (m n : ℕ) (hn : 1 ≤ n) :
    is_m_leafy m (op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain (m * n + 1) (n - 1)) := by
  intro s hs
  rcases op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_subtrees_mem (m * n + 1) (n - 1) hs with rfl | ⟨i, hle, rfl⟩
  · rw [plane_tree_num_internal.eq_1, plane_tree_num_leaves.eq_1]
    omega
  · rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_num_internal,
        op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_num_leaves]
    have : i + 1 ≤ n := by omega
    have : m * (i + 1) ≤ m * n := Nat.mul_le_mul_left m this
    omega

/-- For all m, n ≥ 1, the set mirror_symmetric_m_leafy_trees m n is nonempty. -/
theorem op_1429_mirror_symmetric_m_leafy_trees_nonempty (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (mirror_symmetric_m_leafy_trees m n).Nonempty := by
  refine ⟨op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain (m * n + 1) (n - 1), ?_⟩
  refine ⟨⟨op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_is_m_leafy m n hn, ?_, ?_⟩, ?_⟩
  · rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_num_internal]
    omega
  · rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_num_leaves]
  · rw [op_1429_mirror_symmetric_m_leafy_trees_nonempty_chain_mirror]
