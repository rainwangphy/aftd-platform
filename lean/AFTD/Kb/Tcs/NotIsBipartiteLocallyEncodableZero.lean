import AFTD.Prelude
import AFTD.Kb.Tcs.IsBipartiteLocallyEncodable

/-!
# not_is_bipartite_locally_encodable_zero

Topic: quantum   Node: 155527d8cefa

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec. II.1

For nonempty finite types m and n, the zero vector in EuclideanSpace ℂ (m × n) is not locally encodable.
-/

/-- The zero vector is never locally encodable in a nonempty bipartite space. -/
theorem not_is_bipartite_locally_encodable_zero {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Nonempty m] [Nonempty n] :
    ¬ is_bipartite_locally_encodable (0 : EuclideanSpace ℂ (m × n)) := by
  rintro ⟨B, hB⟩
  inhabit (m × n)
  obtain ⟨uA, uB, h⟩ := hB default
  have hz : B default = 0 := by
    rw [h, map_zero]
  have h1 : ‖B default‖ = 1 := B.orthonormal.1 default
  rw [hz, norm_zero] at h1
  norm_num at h1
