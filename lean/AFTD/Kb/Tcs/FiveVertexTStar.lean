import AFTD.Prelude

/-!
# five_vertex_t_star

Topic: graphs   Node: a99d24c1e985

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

The tree on 5 vertices with edges 0–1, 0–3, 0–4, 1–2: the path 3–0–1–2 with an extra leaf 4 attached at 0.
-/

/-- The T-graph used as the non-degeneracy witness: edges 0-1, 0-3, 0-4, 1-2 on Fin 5. -/
def five_vertex_t_star : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b : Fin 5 =>
    (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 1 ∧ b = 2))
