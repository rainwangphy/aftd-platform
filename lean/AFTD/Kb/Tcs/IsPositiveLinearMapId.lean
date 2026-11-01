import AFTD.Prelude
import AFTD.Kb.Tcs.IsPositiveLinearMap

/-!
# is_positive_linear_map_id

Topic: quantum   Node: 9347bab87571

Provenance: helper lemma. folklore

The identity linear map on d × d complex matrices is positive.
-/

/-- The identity map on d × d complex matrices is a positive linear map. -/
theorem is_positive_linear_map_id (d : ℕ) : is_positive_linear_map d LinearMap.id := fun _ h => h
