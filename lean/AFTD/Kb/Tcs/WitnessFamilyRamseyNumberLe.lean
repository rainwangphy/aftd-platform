import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyNumber
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.WitnessFamilyRamseyProperty

/-!
# witness_family_ramsey_number_le

Topic: combinatorics   Node: 081e15cfe565

Provenance: formalization of a published result. Source: arXiv:2611.15376 Proposition 3.1

For every simple graph G on a type V, natural numbers r, s, t, b, and family W of subsets of Fin r such that every member of W has cardinality t and every s-subset of Fin r contains at least b members of W, if there exists N such that set_coloring_ramsey_property G W.card b 1 N holds, then set_coloring_ramsey_number G r s t ≤ set_coloring_ramsey_number G W.card b 1.
-/

open scoped Classical in
/-- Reduction of generalized set-coloring Ramsey numbers via witness families (Proposition 3.1). -/
theorem witness_family_ramsey_number_le
    {V : Type*} (G : SimpleGraph V)
    (r s t b : ℕ)
    (W : Finset (Finset (Fin r)))
    (hW_card : ∀ w ∈ W, w.card = t)
    (hW_cov : ∀ S : Finset (Fin r), S.card = s → b ≤ (W.filter (· ⊆ S)).card)
    (h_ex : ∃ N, set_coloring_ramsey_property G W.card b 1 N) :
    set_coloring_ramsey_number G r s t ≤ set_coloring_ramsey_number G W.card b 1 := by
  unfold set_coloring_ramsey_number
  apply csInf_le_csInf'
  · obtain ⟨N, hN⟩ := h_ex
    exact ⟨N, hN⟩
  · intro N hN
    exact witness_family_ramsey_property G r s t b N W hW_card hW_cov hN
