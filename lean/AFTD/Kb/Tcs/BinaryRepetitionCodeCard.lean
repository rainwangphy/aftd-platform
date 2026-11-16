import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryRepetitionCode

/-!
# binary_repetition_code_card

Topic: information   Node: 88b7766d633b

Provenance: helper lemma. arXiv:2611.18156 Section IV-A

For an explicit natural number n with 1 ≤ n, the cardinality of the finite set `binary_repetition_code n` is 2.
-/

/-- The binary repetition code of length n ≥ 1 contains exactly 2 codewords. -/
lemma binary_repetition_code_card (n : ℕ) (hn : 1 ≤ n) :
    (binary_repetition_code n).card = 2 := by
  rw [binary_repetition_code]
  apply Finset.card_pair
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  exact Fin.zero_ne_one h0
