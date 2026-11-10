import AFTD.Prelude

/-!
# bpe_full_merge

Topic: algorithms   Node: 98793bc936cb

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

The string obtained by scanning left to right and replacing every available nonoverlapping occurrence of the selected pair with the given symbol.
-/

def bpe_full_merge (a b z : ℕ) : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: y :: xs => if x = a ∧ y = b then z :: bpe_full_merge a b z xs
                    else x :: bpe_full_merge a b z (y :: xs)
