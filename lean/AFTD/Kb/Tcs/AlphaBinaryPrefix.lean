import AFTD.Prelude

/-!
# alpha_binary_prefix

Topic: combinatorics   Node: 7ac48b017a57

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

Encode each positive cell a as one followed by a-1 zero bits, concatenating the blocks.
-/

def alpha_binary_prefix : List ℕ → ℕ
  | [] => 0
  | a :: as => 2 ^ (a - 1 + as.sum) + alpha_binary_prefix as
