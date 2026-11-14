import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyNumber
import AFTD.Kb.Tcs.SetColoringRamseyPropertyOfSucc
import AFTD.Kb.Tcs.SetColoringRamseyProperty

/-!
# set_coloring_ramsey_number_mono_t

Topic: combinatorics   Node: 30534870d3bc

Provenance: formalization of a published result. Source: arXiv:2611.15376 Section 7, Eq (37)

For any simple graph G on a type V and natural numbers r, s, t, if there exists N such that set_coloring_ramsey_property G r s (t + 1) N holds, then set_coloring_ramsey_number G r s t ≤ set_coloring_ramsey_number G r s (t + 1).
-/

open scoped Classical in
/-- Weak monotonicity of the generalized set-coloring Ramsey number in the intersection parameter t (the intersection spectrum inequality). -/
theorem set_coloring_ramsey_number_mono_t
    {V : Type*} (G : SimpleGraph V) (r s t : ℕ)
    (h_ex : ∃ N, set_coloring_ramsey_property G r s (t + 1) N) :
    set_coloring_ramsey_number G r s t ≤ set_coloring_ramsey_number G r s (t + 1) := by
  have h_ne : {N : ℕ | set_coloring_ramsey_property G r s (t + 1) N}.Nonempty := h_ex
  have h_mem := Nat.sInf_mem h_ne
  have h_sub : set_coloring_ramsey_number G r s (t + 1) ∈ {N : ℕ | set_coloring_ramsey_property G r s t N} :=
    set_coloring_ramsey_property_of_succ G r s t _ h_mem
  exact Nat.sInf_le h_sub
