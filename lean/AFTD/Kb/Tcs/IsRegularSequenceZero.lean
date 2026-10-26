import AFTD.Prelude
import AFTD.Kb.Tcs.IsRegularSequence

/-!
# is_regular_sequence_zero

Topic: combinatorics   Node: 37ade3e71cac

Provenance: helper lemma. scout/2610-13103-additive-bases-and-the-zero-sum-invariant-mathsf-n-g-for-gr.md:93

The empty multiset is a regular sequence over any additive commutative group G.
-/

/-- The empty sequence is regular over any additive commutative group. -/
theorem is_regular_sequence_zero {G : Type*} [AddCommGroup G] : IsRegularSequence (0 : Multiset G) := by
  intro _ _
  simp
