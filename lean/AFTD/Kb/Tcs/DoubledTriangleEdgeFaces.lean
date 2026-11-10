import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleFace
import AFTD.Kb.Tcs.DoubledTriangleEdge

/-!
# doubled_triangle_edge_faces

Topic: combinatorics   Node: adeebd98b8f1

Provenance: formalization of a published result. Source: arXiv:2611.12065, Section 2.1

Given an edge e of type DoubledTriangleEdge n in the doubled equilateral triangle triangulation T(n), doubled_triangle_edge_faces returns the ordered pair of faces (DoubledTriangleFace n × DoubledTriangleFace n) incident to e, with boundary edges returning the front and back up faces, and interior edges returning the up face and down face on the same sheet.
-/

/-- The two faces incident to an edge of T(n). -/
def doubled_triangle_edge_faces {n : ℕ} (e : DoubledTriangleEdge n) :
    DoubledTriangleFace n × DoubledTriangleFace n := match e with
  | .horiz_boundary i =>
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
    have h : (i : ℕ) + 0 < n := by omega
    (DoubledTriangleFace.up true i ⟨0, hn⟩ h, DoubledTriangleFace.up false i ⟨0, hn⟩ h)
  | .horiz_interior front i j h hj =>
    have hj_pred : (j : ℕ) - 1 < n := by omega
    have h_down : (i : ℕ) + ((j : ℕ) - 1) + 1 < n := by omega
    (DoubledTriangleFace.up front i j h, DoubledTriangleFace.down front i ⟨(j : ℕ) - 1, hj_pred⟩ h_down)
  | .vert_boundary j =>
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le (j : ℕ)) j.isLt
    have h : 0 + (j : ℕ) < n := by omega
    (DoubledTriangleFace.up true ⟨0, hn⟩ j h, DoubledTriangleFace.up false ⟨0, hn⟩ j h)
  | .vert_interior front i j h hi =>
    have hi_pred : (i : ℕ) - 1 < n := by omega
    have h_down : ((i : ℕ) - 1) + (j : ℕ) + 1 < n := by omega
    (DoubledTriangleFace.up front i j h, DoubledTriangleFace.down front ⟨(i : ℕ) - 1, hi_pred⟩ j h_down)
  | .diag_boundary i =>
    have hj_val : n - 1 - (i : ℕ) < n := by omega
    have h : (i : ℕ) + (n - 1 - (i : ℕ)) < n := by omega
    (DoubledTriangleFace.up true i ⟨n - 1 - (i : ℕ), hj_val⟩ h,
     DoubledTriangleFace.up false i ⟨n - 1 - (i : ℕ), hj_val⟩ h)
  | .diag_interior front i j h =>
    have h_up : (i : ℕ) + j < n := by omega
    (DoubledTriangleFace.up front i j h_up, DoubledTriangleFace.down front i j h)
