import AFTD.Prelude

/-!
# almost_quantum_box_star

Topic: quantum   Node: 1ea548a75278

Provenance: formalization of a published result. Source: arXiv:2610.41448 Table 2

The binary-outcome bipartite box p* on inputs x, y in {1, ..., N} defined by p(0,0|x,x) = 1/17, p(0,1|x,x) = p(1,0|x,x) = 2/17, p(1,1|x,x) = 12/17 for x = y, and p(0,0|x,y) = 0, p(0,1|x,y) = p(1,0|x,y) = 3/17, p(1,1|x,y) = 11/17 for x ≠ y.
-/

/-- The binary-outcome bipartite box p* on N inputs defined in Table 2 of arXiv:2610.41448. -/
noncomputable def almost_quantum_box_star (N : ℕ) (x y : Fin N) (a b : Fin 2) : ℝ := if x = y then
    if a = 0 ∧ b = 0 then 1 / 17
    else if a = 0 ∧ b = 1 then 2 / 17
    else if a = 1 ∧ b = 0 then 2 / 17
    else 12 / 17
  else
    if a = 0 ∧ b = 0 then 0
    else if a = 0 ∧ b = 1 then 3 / 17
    else if a = 1 ∧ b = 0 then 3 / 17
    else 11 / 17
