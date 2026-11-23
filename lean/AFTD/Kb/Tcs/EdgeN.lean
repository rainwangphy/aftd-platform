import AFTD.Prelude

/-!
# EdgeN

Topic: quantum   Node: bb67b99c8bd7

Provenance: formalization of a published result. Source: arXiv:2611.26300

An edge in an edge-coloured quantum graph on $N$ vertices with $D$ colours, specifying two vertices and their respective endpoint colours.
-/

/-- An edge connecting two vertices with specified endpoint colours in a quantum graph. -/
structure EdgeN (N D : ℕ) where
  v1 : Fin N
  v2 : Fin N
  c1 : Fin D
  c2 : Fin D
deriving DecidableEq
