import AFTD.Prelude

/-!
# digraph_arborescence_count_at

Topic: graphs   Node: 1c0ca4abaf6c

Provenance: formalization of a published result. Source: arXiv:2610.25886 (Extremal arborescences in graph orientations), Conjecture 6.1; the rooted counts a_r(D) of Sec. 1

a_r(D): the number of spanning arborescences of D directed towards the root r. Each is recorded by its successor map p: p r = r, every vertex v other than r has the arc v -> p v, and iterating p from any vertex reaches r (so the arcs form a spanning tree oriented towards r).
-/

/-- a_r(D): the number of spanning arborescences of D directed towards the root r. Each is recorded by its successor map p: p r = r, every vertex v other than r has the arc v -> p v, and iterating p from any vertex reaches r (so the arcs form a spanning tree oriented towards r). -/
def digraph_arborescence_count_at {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj]
    (r : Fin n) : ℕ :=
  (Finset.univ.filter (fun p : Fin n → Fin n =>
    p r = r ∧ (∀ v, v ≠ r → D.Adj v (p v)) ∧ ∀ v, p^[n] v = r)).card
