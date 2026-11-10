import AFTD.Prelude
import AFTD.Kb.Tcs.TimelyItem
import AFTD.Kb.Tcs.TimelyItemToTuple

/-!
# instLinearOrderTimelyItem

Topic: online_algorithms   Node: d6f6833abf57

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 1.1 and Section 2

The linear order on `TimelyItem` obtained by pulling back the lexicographic order on `ℝ ×ₗ ℕ ×ₗ ℝ ×ₗ ℝ` along the injective function `timelyItemToTuple`.
-/

/-- Linear order on timely items prioritizing earliest deadline, breaking ties by item id, arrival, and size. -/
noncomputable instance instLinearOrderTimelyItem : LinearOrder TimelyItem := LinearOrder.lift' timelyItemToTuple (by intro ⟨i1, a1, d1, s1⟩ ⟨i2, a2, d2, s2⟩ h; cases h; rfl)
