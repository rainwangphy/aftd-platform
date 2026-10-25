import AFTD.Prelude
import AFTD.Kb.Tcs.Gf8OracleMinTCount
import AFTD.Kb.Tcs.Gf8OracleTCountGe20
import AFTD.Kb.Tcs.Gf8OracleTCountLe29
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.Gf8OracleSyndrome

/-!
# gf8_oracle_min_t_count_ge_20

Topic: quantum   Node: 94904645779c

Provenance: formalization of a published result. Source: arXiv:2610.01024, Proposition 84

The slice-rank lower bound: the minimal T-count of the GF(8) multiplication oracle is at least 20.
-/

/-- The slice-rank lower bound: the minimal T-count of the GF(8) multiplication oracle is at least 20. -/
theorem gf8_oracle_min_t_count_ge_20 : 20 ≤ gf8_oracle_min_t_count := by
  unfold gf8_oracle_min_t_count
  apply le_csInf
  · obtain ⟨S, hS, hc⟩ := gf8_oracle_t_count_le_29
    exact ⟨29, S, hS, hc⟩
  · intro b hb
    obtain ⟨S, hS, rfl⟩ := hb
    exact gf8_oracle_t_count_ge_20 S hS
