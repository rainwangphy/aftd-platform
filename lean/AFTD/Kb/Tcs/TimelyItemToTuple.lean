import AFTD.Prelude
import AFTD.Kb.Tcs.TimelyItem

/-!
# timelyItemToTuple

Topic: online_algorithms   Node: e6d5ecdfb5d8

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 1.1 and Section 2

The tuple representation `timelyItemToTuple` mapping each timely item `p` to the lexicographically ordered tuple `(p.deadline, p.id, p.arrival, p.size)` of type `ℝ ×ₗ ℕ ×ₗ ℝ ×ₗ ℝ` for tie-breaking.
-/

/-- Tupling of a timely item by deadline, id, arrival, and size for lexicographic ordering. -/
def timelyItemToTuple (p : TimelyItem) : ℝ ×ₗ ℕ ×ₗ ℝ ×ₗ ℝ := (p.deadline, p.id, p.arrival, p.size)
