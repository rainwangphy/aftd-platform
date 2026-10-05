import AFTD.Prelude

/-!
# PMAns

Topic: algorithms   Node: faa1cbc71e33

The three possible answers of a comparison query (a, b) on a poset: a ≺ b, b ≺ a, or a ∥ b (incomparable). Setting of arXiv 0707.1532 ("Sorting and Selection in Posets"), Section 4.
-/

/-- The three possible answers of a comparison query `(a, b)` on a poset: `a ≺ b`, `b ≺ a`, or `a ∥ b` (incomparable). Setting of arXiv 0707.1532 ("Sorting and Selection in Posets"), Section 4. -/
inductive PMAns | lt
  | gt
  | inc
  deriving DecidableEq
