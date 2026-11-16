import AFTD.Prelude
import AFTD.Kb.Tcs.LowHalfMul3Bit
import AFTD.Kb.Tcs.LowHalfMul3SixAndCircuit
import AFTD.Kb.Tcs.LowHalfMul3Gate5Expansion

/-!
# low_half_mul3_six_and_upper_bound

Topic: circuits   Node: 3dc0bea01c07

Provenance: formalization of a published result. Source: arXiv:2611.15992 Section 3

For every input vector v : Fin 6 → ZMod 2 and index k : Fin 3, the k-th output of the explicit six-AND circuit low_half_mul3_six_and_circuit v k equals the k-th bit low_half_mul3_bit k v of the three-bit low-half multiplier modulo 8.
-/

/-- Six-AND upper bound for the 3-bit low-half multiplier (PR-1225). -/
theorem low_half_mul3_six_and_upper_bound (v : Fin 6 → ZMod 2) (k : Fin 3) :
    low_half_mul3_six_and_circuit v k = low_half_mul3_bit k v := by
  revert v k
  decide
