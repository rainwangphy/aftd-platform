import AFTD.Prelude

/-!
# star_graph_k1

Topic: graphs   Node: f42dc23289b2

Provenance: formalization of a published result. Source: arXiv:2610.25958

The star graph $K_{1,n}$ with $n$ leaves, centered at `none`, on vertex type `Option (Fin n)`.
-/

/-- The star graph K_{1,n} with n leaves centered at none on vertices Option (Fin n). -/
def star_graph_k1 (n : ℕ) : SimpleGraph (Option (Fin n)) := SimpleGraph.starGraph none
