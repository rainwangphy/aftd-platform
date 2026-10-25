import AFTD.Prelude

/-!
# alpha_signed_cell

Topic: combinatorics   Node: a300f4bc84e2

Provenance: formalization of a published result. Source: Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

A cell of a positive sequence, with alternating signs and zero padding.
-/

def alpha_signed_cell (a : List ℕ) (i : ℕ) : ℤ := if i % 2 = 0 then (a.getD i 0 : ℤ) else -(a.getD i 0 : ℤ)
