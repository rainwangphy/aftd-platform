import AFTD.Prelude

/-!
# pairEncode

Topic: complexity_basics   Node: 56887e255b31

For words w and c over an alphabet Γ, pairEncode w c is the word over Γ ⊕ Unit obtained by writing w, then the single separator symbol Sum.inr (), then c, each of the three parts written with Sum.inl.
-/

/-- Encodes a pair of words (w, c) as a single word over Γ ⊕ Unit, separated by Sum.inr (). -/
def pairEncode {Γ : Type} (w c : List Γ) : List (Γ ⊕ Unit) := List.map Sum.inl w ++ [Sum.inr ()] ++ List.map Sum.inl c
