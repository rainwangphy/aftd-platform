import AFTD.Prelude

/-!
# digraph_out_count

Topic: graphs   Node: 92f7aeb485d0

Provenance: formalization of a published result. Source: arXiv:2610.25886 (Extremal arborescences in graph orientations), Conjecture 6.1; outdegrees

The out-degree of the vertex v of a digraph on Fin n.
-/

/-- The out-degree of the vertex v of a digraph on Fin n. -/
def digraph_out_count {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj] (v : Fin n) : ℕ := (Finset.univ.filter (fun w => D.Adj v w)).card
