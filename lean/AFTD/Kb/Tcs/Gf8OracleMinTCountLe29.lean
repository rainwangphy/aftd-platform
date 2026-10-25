import AFTD.Prelude
import AFTD.Kb.Tcs.Gf8OracleMinTCount
import AFTD.Kb.Tcs.Gf8OracleTCountLe29
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.Gf8OracleSyndrome

/-!
# gf8_oracle_min_t_count_le_29

Topic: quantum   Node: 23e13a790af1

Provenance: formalization of a published result. Source: arXiv:2610.01024, Remark 83 and Table 6

The minimal T-count of the GF(8) multiplication oracle is at most 29, certified by an explicit 29-parity representation.
-/

/-- The upper bound: the minimal T-count of the GF(8) multiplication oracle is at most 29. -/
theorem gf8_oracle_min_t_count_le_29 : gf8_oracle_min_t_count ≤ 29 := Nat.sInf_le gf8_oracle_t_count_le_29
