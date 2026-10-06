import AFTD.Prelude

/-!
# is_regular_diff

Topic: automata   Node: e3681f83e3af

Provenance: formalization of a published result. Source: standard textbook result (automata theory: closure of regular languages under difference)

The difference L1 \\ L2 of two regular languages is regular.
-/

/-- Regular languages are closed under set difference. -/
theorem is_regular_diff {α : Type*} {L1 L2 : Language α} (h1 : L1.IsRegular) (h2 : L2.IsRegular) : (L1 \ L2).IsRegular := by
  rw [sdiff_eq]
  exact h1.inf h2.compl
