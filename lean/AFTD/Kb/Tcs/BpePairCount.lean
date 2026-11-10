import AFTD.Prelude

/-!
# bpe_pair_count

Topic: algorithms   Node: 5e001ededbe4

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

The number of occurrences of the ordered symbol pair replaced by the left-to-right nonoverlapping full merge.
-/

def bpe_pair_count (a b : ℕ) : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: xs => if x = a ∧ y = b then 1 + bpe_pair_count a b xs
                    else bpe_pair_count a b (y :: xs)
