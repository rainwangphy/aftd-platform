import AFTD.Prelude

/-!
# mondrian_seven_rects

Topic: combinatorics   Node: c552c8f8888f

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), equations (2)–(3).

The seven rectangles R₁, …, R₇ of the generic dissection of the n×n square, n = 105q, with a = 7(7q−p), b = 42q, c = 7(7q+p), d = 5(8q−p), e = 5(13q−p), f = (15/2)(7q+p): R₁ = [a,n]×[0,d], R₂ = [0,a]×[0,f], R₃ = [0,c]×[f,n], R₄ = [c,n]×[e,n], R₅ = [b,n]×[d,e], R₆ = [a,b]×[d,f], R₇ = [b,c]×[e,f].
-/

/-- The seven rectangles (2)–(3) of the Pell-family Mondrian dissection. -/
def mondrian_seven_rects (p q : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  [(7 * (7 * q - p), 105 * q, 0, 5 * (8 * q - p)),
   (0, 7 * (7 * q - p), 0, 15 * (7 * q + p) / 2),
   (0, 7 * (7 * q + p), 15 * (7 * q + p) / 2, 105 * q),
   (7 * (7 * q + p), 105 * q, 5 * (13 * q - p), 105 * q),
   (42 * q, 105 * q, 5 * (8 * q - p), 5 * (13 * q - p)),
   (7 * (7 * q - p), 42 * q, 5 * (8 * q - p), 15 * (7 * q + p) / 2),
   (42 * q, 7 * (7 * q + p), 5 * (13 * q - p), 15 * (7 * q + p) / 2)]
