import AFTD.Prelude

/-!
# vertices

Topic: quantum   Node: 404a032d6b42

Provenance: formalization of a published result. Source: arXiv:2611.26300

The canonical list of the $N$ vertices in increasing order.
-/

/-- Canonical list of vertices for K_N. -/
def vertices (N : ℕ) : List (Fin N) := List.finRange N
