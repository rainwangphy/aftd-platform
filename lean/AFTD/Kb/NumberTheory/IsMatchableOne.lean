import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsMatchable

/-!
# is_matchable_one

Topic: elementary_number_theory   Node: 8fad031c8975

Provenance: helper lemma. folklore

The natural number 1 is matchable.
-/

/-- The natural number 1 is matchable. -/
theorem is_matchable_one : is_matchable 1 := by
  unfold is_matchable
  rw [Nat.divisors_one, Finset.card_singleton]
  refine ⟨Equiv.ofUnique _ _, ?_⟩
  intro i
  simp
