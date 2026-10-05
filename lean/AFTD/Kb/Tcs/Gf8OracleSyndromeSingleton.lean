import AFTD.Prelude
import AFTD.Kb.Tcs.Gf8OracleSyndrome

/-!
# gf8_oracle_syndrome_singleton

Topic: quantum   Node: 7cd94e1b3d18

Sanity check: the GF(8) oracle has no order-one syndrome.
-/

theorem gf8_oracle_syndrome_singleton (a : Fin 9) : gf8_oracle_syndrome {a} = 0 := by
  revert a; decide
