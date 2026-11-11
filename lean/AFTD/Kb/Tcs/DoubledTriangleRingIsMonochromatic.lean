import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleRingFaces
import AFTD.Kb.Tcs.DoubledTriangleRing
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_ring_is_monochromatic

Topic: combinatorics   Node: f1846695c343

Provenance: formalization of a published result. Source: arXiv:2611.12065, Lemma 4.3

Given a face coloring C : DoubledTriangleFace n → Bool and a ring R : DoubledTriangleRing n, doubled_triangle_ring_is_monochromatic C R asserts that all faces in doubled_triangle_ring_faces R have color true (black) or all faces have color false (white).
-/

/-- Predicate that a ring R has all its faces assigned the same color under C. -/
def doubled_triangle_ring_is_monochromatic {n : ℕ} (C : DoubledTriangleFace n → Bool)
    (R : DoubledTriangleRing n) : Prop := (∀ f ∈ doubled_triangle_ring_faces R, C f = true) ∨
   (∀ f ∈ doubled_triangle_ring_faces R, C f = false)
