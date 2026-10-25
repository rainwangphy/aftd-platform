import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaSignedCell

/-!
# alpha_lexical_lt

Topic: combinatorics   Node: 14eb0aa65fdc

Provenance: formalization of a published result. Source: Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

The source alternating lexicographic order on positive integer sequences.
-/

def alpha_lexical_lt (a b : List ℕ) : Prop := ∃ i < max a.length b.length,
    (∀ j < i, alpha_signed_cell a j = alpha_signed_cell b j) ∧
      alpha_signed_cell a i < alpha_signed_cell b i
