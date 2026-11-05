import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalFamily
import AFTD.Kb.Tcs.ColoredRootedTree

/-!
# instDecEqIntervalFamily

Topic: data_structures   Node: b6cc0b8012a9

Provenance: formalization of a published result. Source: arXiv:2611.03620 Definition 2.2

Equality on intervals in an interval family is decidable.
-/

/-- DecidableEq instance for the interval index type. -/
instance instDecEqIntervalFamily {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R) : DecidableEq F.ι := F.decEq
