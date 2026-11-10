import AFTD.Prelude

/-!
# bpe_partial_merge

Topic: algorithms   Node: 3e7dab7f4eb6

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

The relation between input and output strings obtained by replacing an arbitrary subset of pairwise nonoverlapping occurrences of the given pair by the given symbol.
-/

def bpe_partial_merge (a b z : ℕ) : List ℕ → List ℕ → Prop
  | [], t => t = []
  | [x], t => t = [x]
  | x :: y :: xs, t =>
      (∃ out, t = x :: out ∧ bpe_partial_merge a b z (y :: xs) out) ∨
      (x = a ∧ y = b ∧ ∃ out, t = z :: out ∧ bpe_partial_merge a b z xs out)
