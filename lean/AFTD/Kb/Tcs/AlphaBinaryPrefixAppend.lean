import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaBinaryPrefix

/-!
# alpha_binary_prefix_append

Topic: combinatorics   Node: 75d5c491ebc9

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

Binary encoding respects concatenation and the sum of the cells is the bit length.
-/

theorem alpha_binary_prefix_append (a b : List ℕ) :
    alpha_binary_prefix (a ++ b) =
      2 ^ b.sum * alpha_binary_prefix a + alpha_binary_prefix b := by
  induction a with
  | nil => simp [alpha_binary_prefix]
  | cons x xs ih =>
    simp only [List.cons_append, alpha_binary_prefix, List.sum_append, ih]
    rw [show x - 1 + (xs.sum + b.sum) = b.sum + (x - 1 + xs.sum) by omega, pow_add]
    ring
