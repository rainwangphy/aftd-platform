import AFTD.Prelude
import AFTD.Kb.Tcs.Gf8OracleSyndrome
import AFTD.Kb.Tcs.Gf8MultCoeff

/-!
# gf8_oracle_syndrome_eq_zero_of_card_ne_three

Topic: quantum   Node: 46c797463010

Provenance: helper lemma. step towards gf8_oracle_t_count_le_23

The syndrome of the GF(8) multiplication oracle vanishes on any subset A ⊆ Fin 9 whose cardinality is not 3, because non-zero syndrome terms arise only from triples connecting the three 3-qubit registers.
-/

/-- The syndrome of the GF(8) multiplication oracle vanishes on any subset whose cardinality is not 3. -/
theorem gf8_oracle_syndrome_eq_zero_of_card_ne_three (A : Finset (Fin 9)) (h : A.card ≠ 3) :
    gf8_oracle_syndrome A = 0 := by
  unfold gf8_oracle_syndrome
  split_ifs with hex
  · exfalso
    apply h
    rcases hex with ⟨q, r, l, -, rfl⟩
    fin_cases q <;> fin_cases r <;> fin_cases l <;> decide
  · rfl
