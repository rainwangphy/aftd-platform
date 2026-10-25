import AFTD.Prelude
import AFTD.Kb.Tcs.IsPermCover

/-!
# is_perm_cover_one

Topic: automata   Node: 59f67da2a341

Provenance: helper lemma. folklore, sanity lemma for is_perm_cover

The singleton set {1} satisfies is_perm_cover 1 {1} for the symmetric group on 1 element.
-/

/-- The singleton {1} is a cover for the symmetric group on 1 element. -/
theorem is_perm_cover_one : is_perm_cover 1 {1} := by
  refine ⟨by simp, fun σ => ⟨1, by simp, ?_⟩⟩
  rw [Subsingleton.elim σ 1, orderOf_one]
