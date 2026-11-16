import AFTD.Prelude
import AFTD.Kb.Tcs.LowMul3Target0
import AFTD.Kb.Tcs.LowMul3Target1
import AFTD.Kb.Tcs.LowMul3Target2

/-!
# lowMul3Targets

Topic: circuits   Node: 2cc51f2226c6

Provenance: formalization of a published result. Source: arXiv:2611.15992 Section 2 (Targets)

The set of target bits {z_0, z_1, z_2} of the three-bit low-half multiplier.
-/

/-- The set of target output functions {z_0, z_1, z_2} for the 3-bit low-half multiplier. -/
def lowMul3Targets : Set ((Fin 6 → Bool) → ZMod 2) := {lowMul3Target0, lowMul3Target1, lowMul3Target2}
