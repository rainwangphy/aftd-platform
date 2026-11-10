import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleFace
import AFTD.Kb.Tcs.DoubledTriangleVertex
import AFTD.Kb.Tcs.DoubledTrianglePointToVertex

/-!
# doubled_triangle_face_vertices

Topic: combinatorics   Node: ad36b05cc3bf

Provenance: formalization of a published result. Source: arXiv:2611.12065, Section 2.3

The set of three vertices incident to a face of the doubled equilateral triangle triangulation T(n).
-/

/-- The three vertices incident to a face of T(n). -/
def doubled_triangle_face_vertices {n : ℕ} (f : DoubledTriangleFace n) : Finset (DoubledTriangleVertex n) := match f with
  | .up front i j h =>
    have h1 : (i : ℕ) + j ≤ n := by omega
    have h2 : ((i : ℕ) + 1) + j ≤ n := by omega
    have h3 : (i : ℕ) + ((j : ℕ) + 1) ≤ n := by omega
    have i_lt : (i : ℕ) < n + 1 := by omega
    have j_lt : (j : ℕ) < n + 1 := by omega
    have i1_lt : (i : ℕ) + 1 < n + 1 := by omega
    have j1_lt : (j : ℕ) + 1 < n + 1 := by omega
    { doubled_triangle_point_to_vertex front ⟨i, i_lt⟩ ⟨j, j_lt⟩ h1,
      doubled_triangle_point_to_vertex front ⟨(i : ℕ) + 1, i1_lt⟩ ⟨j, j_lt⟩ h2,
      doubled_triangle_point_to_vertex front ⟨i, i_lt⟩ ⟨(j : ℕ) + 1, j1_lt⟩ h3 }
  | .down front i j h =>
    have h1 : ((i : ℕ) + 1) + j ≤ n := by omega
    have h2 : (i : ℕ) + ((j : ℕ) + 1) ≤ n := by omega
    have h3 : ((i : ℕ) + 1) + ((j : ℕ) + 1) ≤ n := by omega
    have i_lt : (i : ℕ) < n + 1 := by omega
    have j_lt : (j : ℕ) < n + 1 := by omega
    have i1_lt : (i : ℕ) + 1 < n + 1 := by omega
    have j1_lt : (j : ℕ) + 1 < n + 1 := by omega
    { doubled_triangle_point_to_vertex front ⟨(i : ℕ) + 1, i1_lt⟩ ⟨j, j_lt⟩ h1,
      doubled_triangle_point_to_vertex front ⟨i, i_lt⟩ ⟨(j : ℕ) + 1, j1_lt⟩ h2,
      doubled_triangle_point_to_vertex front ⟨(i : ℕ) + 1, i1_lt⟩ ⟨(j : ℕ) + 1, j1_lt⟩ h3 }
