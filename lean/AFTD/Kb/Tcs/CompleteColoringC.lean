import AFTD.Prelude

/-!
# complete_coloring_C

Topic: quantum   Node: 2f83cc2e26f8

Provenance: formalization of a published result. Source: arXiv:2611.19002, Quantum Coloring Games on Complete Graphs, Section 3.2

The minimum sum of squared fiber sizes across m colors for n inputs, (m - r) q^2 + r (q + 1)^2 where q = floor(n/m) and r = n mod m.
-/

/-- Minimum sum of squares of color occupancies for n inputs and m colors. -/
def complete_coloring_C (n m : ℕ) : ℕ :=
  let q := n / m
  let r := n % m
  (m - r) * q ^ 2 + r * (q + 1) ^ 2
