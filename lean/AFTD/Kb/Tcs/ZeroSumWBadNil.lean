import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumWBad

/-!
# zero_sum_w_bad_nil

Topic: combinatorics   Node: e1c58aba4244

Provenance: helper lemma. Sanity lemma for w-bad sequences, arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems).

The empty sequence is w-bad.
-/

theorem zero_sum_w_bad_nil (n r : ℕ) : zero_sum_w_bad n ([] : List (Fin r → ℤ)) := by
  dsimp [zero_sum_w_bad, zero_sum_admissible, zero_sum_good_subseq]
  constructor
  · intro a ha
    cases ha
  · intro I hI
    obtain ⟨⟨x, _⟩, _⟩ := hI
    exact Fin.elim0 x
