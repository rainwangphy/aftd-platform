import AFTD.Prelude
import AFTD.Kb.Tcs.HasNondegenerateGp3

/-!
# not_has_nondegenerate_gp3_empty

Topic: combinatorics   Node: dd6a8493b6a3

Provenance: helper lemma. arXiv:2610.34758, Definition 1.1

The empty set contains no nondegenerate three-term geometric progression.
-/

/-- The empty set contains no nondegenerate three-term geometric progression. -/
theorem not_has_nondegenerate_gp3_empty {F : Type*} [CommRing F] :
    ¬ has_nondegenerate_gp3 (∅ : Set F) := by
  intro ⟨x, r, _, _, _, h, _⟩
  exact h
