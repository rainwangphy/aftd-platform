import AFTD.Prelude

/-!
# digit_exchange_walsh_limit

Topic: cryptography   Node: 9617571cdc14

Provenance: original. Related work: arXiv:2611.02572

The proposed limiting probability digit_exchange_walsh_limit j for the binary Walsh magnitude j * 2^m of the digit-exchange permutation, defined for j from 0 to 6 as 361/768, 49/120, 161/1536, 1/72, 11/3840, 0, and 1/23040, and 0 for j >= 7.
-/

/-- Conjectured limiting probabilities of normalized Walsh magnitudes |W|/q for j = 0,...,6. -/
def digit_exchange_walsh_limit (j : ℕ) : ℚ :=
  match j with
  | 0 => 361 / 768
  | 1 => 49 / 120
  | 2 => 161 / 1536
  | 3 => 1 / 72
  | 4 => 11 / 3840
  | 5 => 0
  | 6 => 1 / 23040
  | _ => 0
