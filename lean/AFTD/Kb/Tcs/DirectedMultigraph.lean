import AFTD.Prelude

/-!
# DirectedMultigraph

Topic: graphs   Node: 17cf1043013f

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 2

A directed multigraph parameterized by vertex type V and edge type E, with source and target maps src : E → V and tgt : E → V.
-/

/-- A directed multigraph with vertex type V and edge type E. -/
structure DirectedMultigraph (V E : Type*) where
  src : E → V
  tgt : E → V
