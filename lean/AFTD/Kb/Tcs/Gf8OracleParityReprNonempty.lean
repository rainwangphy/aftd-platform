import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.Gf8OracleSyndrome
import AFTD.Kb.Tcs.Gf8OracleSyndromeZeroZeroZero

/-!
# gf8_oracle_parity_repr_nonempty

Topic: quantum   Node: 2092b5e926fa

Provenance: helper lemma. step towards gf8_oracle_t_count_le_23

Every parity representation S of the GF(8) multiplication oracle syndrome is nonempty because the syndrome at {0, 3, 6} is 1 mod 2, whereas an empty representation would yield moment 0.
-/

/-- Every parity representation of the GF(8) multiplication oracle syndrome is nonempty. -/
theorem gf8_oracle_parity_repr_nonempty (S : Finset (Finset (Fin 9)))
    (hS : is_parity_repr S gf8_oracle_syndrome) : S.Nonempty := by
  rcases hS with ⟨-, hmom⟩
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  subst h
  have hm := hmom ({0, 3, 6} : Finset (Fin 9)) ⟨by decide, by decide⟩
  rw [gf8_oracle_syndrome_zero_zero_zero] at hm
  simp at hm
