import AFTD.Prelude

/-!
# alpha_lexical_meet

Topic: combinatorics   Node: b8db4f861b2d

Provenance: formalization of a published result. Source: Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

The common left factor, including the minimum value at the first unequal cell.
-/

def alpha_lexical_meet : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs => if a = b then a :: alpha_lexical_meet as bs else [min a b]
  | _, _ => []
