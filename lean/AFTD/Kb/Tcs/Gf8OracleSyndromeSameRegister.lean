import AFTD.Prelude
import AFTD.Kb.Tcs.Gf8OracleSyndrome

/-!
# gf8_oracle_syndrome_same_register

Topic: quantum   Node: 90afcf97b32a

Sanity check: the syndrome of the GF(8) oracle vanishes on a triple inside one register.
-/

theorem gf8_oracle_syndrome_same_register : gf8_oracle_syndrome {0, 1, 2} = 0 := by decide
