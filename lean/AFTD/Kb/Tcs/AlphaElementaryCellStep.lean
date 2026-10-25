import AFTD.Prelude

/-!
# alpha_elementary_cell_step

Topic: combinatorics   Node: 87e5ef2efc18

Provenance: formalization of a published result. Source: Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

One source elementary split or conjugation, with a zero-based cell index.
-/

def alpha_elementary_cell_step (a b : List ℕ) (i : ℕ) : Prop := i < a.length ∧
    ((1 < a.getD i 0 ∧
      b = a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)) ∨
    (0 < i ∧ a.getD i 0 = 1 ∧
      b = a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1)))
