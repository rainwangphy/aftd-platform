import AFTD.Prelude

/-!
# k_plus_graph

Topic: graphs   Node: 2f7b626367ed

Provenance: formalization of a published result. Source: arXiv:2610.40279 Section 1

The graph K_s^+ is obtained from a complete graph on s vertices by adding one vertex adjacent to exactly one clique vertex.
-/

/-- The graph K_s^+ obtained from K_s by adding a vertex adjacent to exactly one clique vertex. -/
def k_plus_graph (s : ℕ) : SimpleGraph (Option (Fin s)) :=
  SimpleGraph.fromRel fun u v =>
    match u, v with
    | some i, some j => i ≠ j
    | some i, none => (i : ℕ) = 0
    | none, some j => (j : ℕ) = 0
    | none, none => False
