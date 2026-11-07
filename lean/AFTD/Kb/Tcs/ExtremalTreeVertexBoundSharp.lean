import AFTD.Prelude
import AFTD.Kb.Tcs.ExtremalTreeVertexBound
import AFTD.Kb.Tcs.BinaryTreeLabels
import AFTD.Kb.Tcs.BinaryTreeNoAncestorDescendantRepeat
import AFTD.Kb.Tcs.BinaryTreeBoundedChildOverlap

/-!
# extremal_tree_vertex_bound_sharp

Topic: combinatorics   Node: e4178d9a8f78

Provenance: formalization of a published result. Source: arXiv:2611.04184 Theorem 4.6 (Short permutation pattern waves: The complete length-five classification)

For any natural numbers C and q, there exists a binary tree t : BinaryTree ℕ such that (binary_tree_labels t).card ≤ q, binary_tree_no_ancestor_descendant_repeat t, binary_tree_bounded_child_overlap C t, and t.numNodes = extremal_tree_vertex_bound C q.
-/

open BinaryTree

def extremal_tree_vertex_bound_sharp_completeBinaryTree : ℕ → BinaryTree ℕ
  | 0 => .nil
  | k + 1 => .node k (extremal_tree_vertex_bound_sharp_completeBinaryTree k) (extremal_tree_vertex_bound_sharp_completeBinaryTree k)

def extremal_tree_vertex_bound_sharp_extTree (C : ℕ) : ℕ → BinaryTree ℕ
  | 0 => extremal_tree_vertex_bound_sharp_completeBinaryTree C
  | d + 1 => .node (C + d) (extremal_tree_vertex_bound_sharp_completeBinaryTree C) (extremal_tree_vertex_bound_sharp_extTree C d)

theorem extremal_tree_vertex_bound_sharp_complete_labels (k : ℕ) :
    binary_tree_labels (extremal_tree_vertex_bound_sharp_completeBinaryTree k) = Finset.range k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [extremal_tree_vertex_bound_sharp_completeBinaryTree, binary_tree_labels, ih, Finset.range_add_one]

theorem extremal_tree_vertex_bound_sharp_complete_no_repeat (k : ℕ) :
    binary_tree_no_ancestor_descendant_repeat (extremal_tree_vertex_bound_sharp_completeBinaryTree k) := by
  induction k with
  | zero => simp [extremal_tree_vertex_bound_sharp_completeBinaryTree, binary_tree_no_ancestor_descendant_repeat]
  | succ k ih =>
    simp [extremal_tree_vertex_bound_sharp_completeBinaryTree, binary_tree_no_ancestor_descendant_repeat,
      extremal_tree_vertex_bound_sharp_complete_labels, ih]

theorem extremal_tree_vertex_bound_sharp_complete_bounded_overlap (C : ℕ) {k : ℕ} (h : k ≤ C) :
    binary_tree_bounded_child_overlap C (extremal_tree_vertex_bound_sharp_completeBinaryTree k) := by
  induction k with
  | zero => simp [extremal_tree_vertex_bound_sharp_completeBinaryTree, binary_tree_bounded_child_overlap]
  | succ k ih =>
    have hk : k ≤ C := Nat.le_of_succ_le h
    simp [extremal_tree_vertex_bound_sharp_completeBinaryTree, binary_tree_bounded_child_overlap,
      extremal_tree_vertex_bound_sharp_complete_labels, ih hk]
    exact Nat.le_trans (Nat.le_succ k) h

theorem extremal_tree_vertex_bound_sharp_complete_numNodes (k : ℕ) :
    (extremal_tree_vertex_bound_sharp_completeBinaryTree k).numNodes = 2 ^ k - 1 := by
  induction k with
  | zero => simp [extremal_tree_vertex_bound_sharp_completeBinaryTree]
  | succ k ih =>
    simp [extremal_tree_vertex_bound_sharp_completeBinaryTree, numNodes, ih]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

theorem extremal_tree_vertex_bound_sharp_ext_labels (C d : ℕ) :
    binary_tree_labels (extremal_tree_vertex_bound_sharp_extTree C d) = Finset.range (C + d) := by
  induction d with
  | zero => simp [extremal_tree_vertex_bound_sharp_extTree, extremal_tree_vertex_bound_sharp_complete_labels]
  | succ d ih =>
    have hsub : Finset.range C ⊆ Finset.range (C + d) := Finset.range_mono (Nat.le_add_right C d)
    have : C + (d + 1) = (C + d) + 1 := by omega
    rw [this, Finset.range_add_one]
    simp [extremal_tree_vertex_bound_sharp_extTree, binary_tree_labels,
      extremal_tree_vertex_bound_sharp_complete_labels, ih, Finset.union_eq_right.mpr hsub]

theorem extremal_tree_vertex_bound_sharp_ext_no_repeat (C d : ℕ) :
    binary_tree_no_ancestor_descendant_repeat (extremal_tree_vertex_bound_sharp_extTree C d) := by
  induction d with
  | zero => simp [extremal_tree_vertex_bound_sharp_extTree, extremal_tree_vertex_bound_sharp_complete_no_repeat]
  | succ d ih =>
    simp only [extremal_tree_vertex_bound_sharp_extTree, binary_tree_no_ancestor_descendant_repeat,
      extremal_tree_vertex_bound_sharp_complete_labels, extremal_tree_vertex_bound_sharp_ext_labels,
      Finset.mem_range, not_lt]
    refine ⟨by omega, by omega, extremal_tree_vertex_bound_sharp_complete_no_repeat C, ih⟩

theorem extremal_tree_vertex_bound_sharp_ext_bounded_overlap (C d : ℕ) :
    binary_tree_bounded_child_overlap C (extremal_tree_vertex_bound_sharp_extTree C d) := by
  induction d with
  | zero => exact extremal_tree_vertex_bound_sharp_complete_bounded_overlap C le_rfl
  | succ d ih =>
    have hsub : Finset.range C ⊆ Finset.range (C + d) := Finset.range_mono (Nat.le_add_right C d)
    simp only [extremal_tree_vertex_bound_sharp_extTree, binary_tree_bounded_child_overlap,
      extremal_tree_vertex_bound_sharp_complete_labels, extremal_tree_vertex_bound_sharp_ext_labels,
      Finset.inter_eq_left.mpr hsub, Finset.card_range]
    exact ⟨le_rfl, extremal_tree_vertex_bound_sharp_complete_bounded_overlap C le_rfl, ih⟩

theorem extremal_tree_vertex_bound_sharp_ext_numNodes (C d : ℕ) :
    (extremal_tree_vertex_bound_sharp_extTree C d).numNodes = (2 ^ C - 1) + 2 ^ C * d := by
  induction d with
  | zero => simp [extremal_tree_vertex_bound_sharp_extTree, extremal_tree_vertex_bound_sharp_complete_numNodes]
  | succ d ih =>
    simp only [extremal_tree_vertex_bound_sharp_extTree, numNodes, extremal_tree_vertex_bound_sharp_complete_numNodes, ih]
    have : 1 ≤ 2 ^ C := Nat.one_le_two_pow
    have : 2 ^ C * (d + 1) = 2 ^ C * d + 2 ^ C := mul_add_one (2 ^ C) d
    omega

/-- Sharpness of the extremal vertex bound for binary trees with bounded child-subtree overlap (Theorem 4.6). -/
theorem extremal_tree_vertex_bound_sharp (C q : ℕ) :
    ∃ (t : BinaryTree ℕ),
      (binary_tree_labels t).card ≤ q ∧
      binary_tree_no_ancestor_descendant_repeat t ∧
      binary_tree_bounded_child_overlap C t ∧
      t.numNodes = extremal_tree_vertex_bound C q := by
  by_cases hq : q ≤ C
  · use extremal_tree_vertex_bound_sharp_completeBinaryTree q
    refine ⟨?_, extremal_tree_vertex_bound_sharp_complete_no_repeat q,
      extremal_tree_vertex_bound_sharp_complete_bounded_overlap C hq, ?_⟩
    · rw [extremal_tree_vertex_bound_sharp_complete_labels, Finset.card_range]
    · rw [extremal_tree_vertex_bound_sharp_complete_numNodes, extremal_tree_vertex_bound, if_pos hq]
  · use extremal_tree_vertex_bound_sharp_extTree C (q - C)
    have hCq : C ≤ q := le_of_not_ge hq
    have hCd : C + (q - C) = q := Nat.add_sub_of_le hCq
    refine ⟨?_, extremal_tree_vertex_bound_sharp_ext_no_repeat C (q - C),
      extremal_tree_vertex_bound_sharp_ext_bounded_overlap C (q - C), ?_⟩
    · rw [extremal_tree_vertex_bound_sharp_ext_labels, hCd, Finset.card_range]
    · rw [extremal_tree_vertex_bound_sharp_ext_numNodes, extremal_tree_vertex_bound, if_neg hq]
