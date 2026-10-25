import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_arbitrary_symmetric_intervals_obstruction

Topic: combinatorics   Node: 397b8bdfaef8

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

Two separate rank reflections need not compose to a one-bit Gray-word difference.
-/

theorem brgc_arbitrary_symmetric_intervals_obstruction :
    brgc_word 1 ^^^ brgc_word 6 = 4 ∧
    brgc_word 5 ^^^ brgc_word 10 = 8 ∧
    brgc_word 1 ^^^ brgc_word 10 = 14 ∧
    ¬ ∃ i : Fin 4, brgc_word 1 ^^^ brgc_word 10 = 2 ^ i.val := by
  decide
