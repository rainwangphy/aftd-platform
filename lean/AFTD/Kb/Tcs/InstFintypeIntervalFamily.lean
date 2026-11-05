import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalFamily
import AFTD.Kb.Tcs.ColoredRootedTree

/-!
# instFintypeIntervalFamily

Topic: data_structures   Node: 70b5546d232c

Provenance: formalization of a published result. Source: arXiv:2611.03620 Definition 2.2

The collection of intervals in an interval family is finite.
-/

/-- Fintype instance for the interval index type. -/
instance instFintypeIntervalFamily {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R) : Fintype F.ι := F.fintype
