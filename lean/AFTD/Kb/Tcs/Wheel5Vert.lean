import AFTD.Prelude

/-!
# Wheel5Vert

Topic: graphs   Node: e0c14215abfd

Provenance: formalization of a published result. Source: arXiv:2611.03236 Sec. 3

The vertex set of the 5-wheel W₅, consisting of a central vertex u and five rim vertices v 0, ..., v 4.
-/

/-- The vertex set of the 5-wheel W₅: center u and 5 rim vertices v 0, ..., v 4. -/
inductive Wheel5Vert : Type | u : Wheel5Vert
  | v : Fin 5 → Wheel5Vert
  deriving DecidableEq, Fintype
