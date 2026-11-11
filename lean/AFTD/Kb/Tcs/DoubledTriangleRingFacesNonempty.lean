import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleRingFaces
import AFTD.Kb.Tcs.DoubledTriangleRing
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_ring_faces_nonempty

Topic: combinatorics   Node: 9a925009d3d6

Provenance: helper lemma. arXiv:2611.12065, Section 4.1

For any integer n > 0, for every ring R : DoubledTriangleRing n of T(n), the set of faces doubled_triangle_ring_faces R is nonempty.
-/

/-- Every ring of T(n) has at least one face when n > 0. -/
theorem doubled_triangle_ring_faces_nonempty {n : ℕ} (hn : 0 < n) (R : DoubledTriangleRing n) :
    (doubled_triangle_ring_faces R).Nonempty := by
  cases R with
  | x k =>
    have hk : (k : ℕ) < n := k.isLt
    have h_sum : (k : ℕ) + ((⟨0, hn⟩ : Fin n) : ℕ) < n := by dsimp; omega
    refine ⟨DoubledTriangleFace.up true k ⟨0, hn⟩ h_sum, ?_⟩
    simp [doubled_triangle_ring_faces]
  | y k =>
    have hk : (k : ℕ) < n := k.isLt
    have h_sum : ((⟨0, hn⟩ : Fin n) : ℕ) + (k : ℕ) < n := by dsimp; omega
    refine ⟨DoubledTriangleFace.up true ⟨0, hn⟩ k h_sum, ?_⟩
    simp [doubled_triangle_ring_faces]
  | z k =>
    have hk : (k : ℕ) < n := k.isLt
    have h_lt : n - 1 - (k : ℕ) < n := by omega
    have h_sum : ((⟨n - 1 - (k : ℕ), h_lt⟩ : Fin n) : ℕ) + ((⟨0, hn⟩ : Fin n) : ℕ) < n := by dsimp; omega
    refine ⟨DoubledTriangleFace.up true ⟨n - 1 - (k : ℕ), h_lt⟩ ⟨0, hn⟩ h_sum, ?_⟩
    simp [doubled_triangle_ring_faces]
    omega
