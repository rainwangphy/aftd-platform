import AFTD.Prelude
import AFTD.Kb.Tcs.Gf8OracleSyndrome

/-!
# gf8_oracle_syndrome_zero_zero_zero

Topic: quantum   Node: 2d4351a19074

Sanity check: the syndrome of the GF(8) oracle is 1 on {x_0, y_0, z_0}, since 1 * 1 = 1 has bit 0 set.
-/

theorem gf8_oracle_syndrome_zero_zero_zero : gf8_oracle_syndrome {0, 3, 6} = 1 := by decide
