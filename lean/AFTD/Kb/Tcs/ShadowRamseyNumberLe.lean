import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyNumber
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.ShadowRamseyProperty
import AFTD.Kb.Tcs.WitnessFamilyRamseyNumberLe

/-!
# shadow_ramsey_number_le

Topic: combinatorics   Node: c126dda3ade6

Provenance: formalization of a published result. Source: arXiv:2611.15376 Proposition 3.1

For every simple graph G on a type V and natural numbers r, s, t, if there exists N such that set_coloring_ramsey_property G (r.choose t) (s.choose t) 1 N holds, then the generalized set-coloring Ramsey number satisfies set_coloring_ramsey_number G r s t ≤ set_coloring_ramsey_number G (r.choose t) (s.choose t) 1.
-/

open scoped Classical in
/-- The shadow inequality for generalized set-coloring Ramsey numbers. -/
theorem shadow_ramsey_number_le
    {V : Type*} (G : SimpleGraph V)
    (r s t : ℕ)
    (h_ex : ∃ N, set_coloring_ramsey_property G (r.choose t) (s.choose t) 1 N) :
    set_coloring_ramsey_number G r s t ≤ set_coloring_ramsey_number G (r.choose t) (s.choose t) 1 := by
  unfold set_coloring_ramsey_number
  apply csInf_le_csInf'
  · obtain ⟨N, hN⟩ := h_ex
    exact ⟨N, hN⟩
  · intro N hN
    exact shadow_ramsey_property G r s t N hN
