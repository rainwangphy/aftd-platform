import AFTD.Prelude
import AFTD.Kb.Tcs.TimelyItemToTuple
import AFTD.Kb.Tcs.TimelyItem

/-!
# timelyItemToTuple_injective

Topic: online_algorithms   Node: 14fab35d1a20

Provenance: helper lemma. folklore

The mapping `timelyItemToTuple` from timely items to lexicographically ordered tuples `ℝ ×ₗ ℕ ×ₗ ℝ ×ₗ ℝ` is injective.
-/

/-- Injectivity of timelyItemToTuple. -/
theorem timelyItemToTuple_injective : Function.Injective timelyItemToTuple := by
  intro p q h
  cases p with
  | mk id1 arr1 dl1 sz1 =>
  cases q with
  | mk id2 arr2 dl2 sz2 =>
  simp only [timelyItemToTuple] at h
  cases h
  rfl
