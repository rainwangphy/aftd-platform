import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleRing
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_ring_faces

Topic: combinatorics   Node: 54223ee353b3

Provenance: formalization of a published result. Source: arXiv:2611.12065, Definition 4.1

Given a ring R of type DoubledTriangleRing n, doubled_triangle_ring_faces R returns the finite set of faces f : DoubledTriangleFace n belonging to R: for an x-ring .x k, faces with first coordinate i = k; for a y-ring .y k, faces with second coordinate j = k; and for a z-ring .z k (the strip k ≤ z ≤ k+1 where z = n - x - y), up-faces satisfying i + j + k + 1 = n and down-faces satisfying i + j + k + 2 = n.
-/

/-- The finite set of faces of T(n) lying in a ring R. -/
def doubled_triangle_ring_faces {n : ℕ} (R : DoubledTriangleRing n) : Finset (DoubledTriangleFace n) := Finset.univ.filter (fun f =>
    (match R, f with
    | .x k, .up _ i _ _ => i == k
    | .x k, .down _ i _ _ => i == k
    | .y k, .up _ _ j _ => j == k
    | .y k, .down _ _ j _ => j == k
    | .z k, .up _ i j _ => (i : ℕ) + (j : ℕ) + (k : ℕ) + 1 == n
    | .z k, .down _ i j _ => (i : ℕ) + (j : ℕ) + (k : ℕ) + 2 == n) = true)
