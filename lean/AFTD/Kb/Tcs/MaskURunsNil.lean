import AFTD.Prelude
import AFTD.Kb.Tcs.MaskURuns

/-!
# mask_u_runs_nil

Topic: automata   Node: 427d1226cb75

Provenance: helper lemma. folklore

An empty binary mask has zero U-runs: mask_u_runs [] = 0.
-/

/-- An empty binary mask has zero U-runs. -/
theorem mask_u_runs_nil : mask_u_runs [] = 0 := by rfl
