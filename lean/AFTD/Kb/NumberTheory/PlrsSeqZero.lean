import AFTD.Prelude
import AFTD.Kb.NumberTheory.PlrsSeq

/-!
# plrs_seq_zero

Topic: elementary_number_theory   Node: 9647c20142b6

Provenance: helper lemma. arXiv:2611.10200, Section 1

For any list of natural numbers c : List ℕ, plrs_seq c 0 = 0.
-/

/-- The base value of plrs_seq at index 0 is 0. -/
theorem plrs_seq_zero (c : List ℕ) : plrs_seq c 0 = 0 := plrs_seq.eq_1 c
