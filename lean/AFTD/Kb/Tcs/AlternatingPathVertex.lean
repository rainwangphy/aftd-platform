import AFTD.Prelude

/-!
# alternating_path_vertex

Topic: graphs   Node: 15b5506c857a

Provenance: formalization of a published result. Source: arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

The m-th vertex in the alternating path AP_n is m/2 if m is even, and n - 1 - m/2 if m is odd.
-/

/-- The m-th vertex in the alternating path AP_n on Fin n. -/
def alternating_path_vertex (n : ℕ) (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else n - 1 - m / 2
