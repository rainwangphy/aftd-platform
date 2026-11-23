import AFTD.Prelude

/-!
# lex_ge

Topic: social_choice   Node: c983614b3ba1

Provenance: formalization of a published result. Source: arXiv:2611.19021 Section 2.3

A binary relation on lists of natural numbers defined recursively: lex_ge [] [] is True; lex_ge [] (_ :: _) is False; lex_ge (_ :: _) [] is True; and for non-empty lists, lex_ge (a :: as) (b :: bs) holds if a > b or (a = b and lex_ge as bs).
-/

/-- Lexicographical comparison of lists of natural numbers. -/
def lex_ge : List ℕ → List ℕ → Prop
| [], [] => True
| [], _ :: _ => False
| _ :: _, [] => True
| a :: as, b :: bs => a > b ∨ (a = b ∧ lex_ge as bs)
