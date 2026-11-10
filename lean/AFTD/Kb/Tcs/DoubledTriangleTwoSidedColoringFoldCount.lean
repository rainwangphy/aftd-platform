import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleTwoSidedColoring
import AFTD.Kb.Tcs.DoubledTriangleFoldCount
import AFTD.Kb.Tcs.DoubledTriangleEdge
import AFTD.Kb.Tcs.DoubledTriangleEdgeFaces
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_two_sided_coloring_fold_count

Topic: combinatorics   Node: cf31940002d4

Provenance: formalization of a published result. Source: arXiv:2611.12065, Proposition 3.3

For every natural number $n$, the fold count of the two-sided coloring of the doubled triangle triangulation of size $n$ is equal to $3n$.
-/

/-- The fold count of the two-sided coloring B_n of T(n) is 3n. -/
theorem doubled_triangle_two_sided_coloring_fold_count (n : ℕ) :
    doubled_triangle_fold_count (doubled_triangle_two_sided_coloring n) = 3 * n := by
  classical
  unfold doubled_triangle_fold_count
  have hset :
      (Finset.univ.filter (fun e : DoubledTriangleEdge n =>
        doubled_triangle_two_sided_coloring n (doubled_triangle_edge_faces e).1 ≠
        doubled_triangle_two_sided_coloring n (doubled_triangle_edge_faces e).2))
      = (Finset.univ.image DoubledTriangleEdge.horiz_boundary ∪
         Finset.univ.image DoubledTriangleEdge.vert_boundary) ∪
         Finset.univ.image DoubledTriangleEdge.diag_boundary := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
    cases e <;> simp [doubled_triangle_edge_faces, doubled_triangle_two_sided_coloring]
  rw [hset]
  have hd1 : Disjoint (Finset.univ.image (DoubledTriangleEdge.horiz_boundary (n := n)))
      (Finset.univ.image (DoubledTriangleEdge.vert_boundary (n := n))) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at he1 he2
    obtain ⟨a, rfl⟩ := he1
    obtain ⟨b, hb⟩ := he2
    exact nomatch hb
  have hd2 : Disjoint (Finset.univ.image (DoubledTriangleEdge.horiz_boundary (n := n)) ∪
      Finset.univ.image (DoubledTriangleEdge.vert_boundary (n := n)))
      (Finset.univ.image (DoubledTriangleEdge.diag_boundary (n := n))) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he1 he2
    rcases he1 with he1 | he1
    · obtain ⟨a, rfl⟩ := he1
      obtain ⟨b, hb⟩ := he2
      exact nomatch hb
    · obtain ⟨a, rfl⟩ := he1
      obtain ⟨b, hb⟩ := he2
      exact nomatch hb
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Finset.card_image_of_injective _ (fun a b h => DoubledTriangleEdge.horiz_boundary.inj h),
    Finset.card_image_of_injective _ (fun a b h => DoubledTriangleEdge.vert_boundary.inj h),
    Finset.card_image_of_injective _ (fun a b h => DoubledTriangleEdge.diag_boundary.inj h)]
  simp [Finset.card_univ]
  omega
