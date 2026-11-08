import AFTD.Prelude

/-!
# l_path_graph

Topic: graphs   Node: f0cd51df67ed

Provenance: formalization of a published result. Source: arXiv:2610.40279 Section 1

The graph L_t is obtained from a complete graph on t vertices by attaching a path of length two to one clique vertex.
-/

/-- The graph L_t obtained from K_t by attaching a path of length two to one clique vertex. -/
def l_path_graph (t : ℕ) : SimpleGraph (Sum (Fin t) (Fin 2)) :=
  SimpleGraph.fromRel fun u v =>
    match u, v with
    | Sum.inl i, Sum.inl j => i ≠ j
    | Sum.inl i, Sum.inr 0 => (i : ℕ) = 0
    | Sum.inr 0, Sum.inl j => (j : ℕ) = 0
    | Sum.inr 0, Sum.inr 1 => True
    | Sum.inr 1, Sum.inr 0 => True
    | _, _ => False
