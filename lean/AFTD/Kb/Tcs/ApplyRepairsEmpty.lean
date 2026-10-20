import AFTD.Prelude
import AFTD.Kb.Tcs.ApplyRepairs
import AFTD.Kb.Tcs.ConflictNeighborhood

/-!
# apply_repairs_empty

Topic: approximation   Node: 338deb52af7a

Provenance: helper lemma. folklore

For any type α with decidable equality and family A : Finset (Finset α), applying the empty repair family to A yields A.
-/

/-- Applying the empty repair family leaves the packing unchanged. -/
theorem apply_repairs_empty {α : Type*} [DecidableEq α] (A : Finset (Finset α)) : apply_repairs A ∅ = A := by
  simp [apply_repairs, conflict_neighborhood]
