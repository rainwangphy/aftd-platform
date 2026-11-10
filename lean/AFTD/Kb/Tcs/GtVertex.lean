import AFTD.Prelude

/-!
# GtVertex

Topic: graphs   Node: d918aa445aae

Provenance: formalization of a published result. Source: arXiv:2611.11352 Definition 2

The vertex set of the graph G_t partitioned into blocks A (size 3), B (size 2), C (size 2), D (size 3), P (size t), Q (size t), and R (size t).
-/

/-- Vertex set of the graph G_t. -/
inductive GtVertex (t : ℕ) : Type | A (i : Fin 3)
  | B (i : Fin 2)
  | C (i : Fin 2)
  | D (i : Fin 3)
  | P (i : Fin t)
  | Q (i : Fin t)
  | R (i : Fin t)
deriving DecidableEq, Fintype
