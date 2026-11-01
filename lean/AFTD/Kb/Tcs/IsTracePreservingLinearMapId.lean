import AFTD.Prelude
import AFTD.Kb.Tcs.IsTracePreservingLinearMap

/-!
# is_trace_preserving_linear_map_id

Topic: quantum   Node: 96bcef77645a

Provenance: helper lemma. folklore

The identity linear map on d × d complex matrices is trace-preserving.
-/

/-- The identity map on d × d complex matrices is trace-preserving. -/
theorem is_trace_preserving_linear_map_id (d : ℕ) : is_trace_preserving_linear_map d LinearMap.id := by
  intro X
  rfl
