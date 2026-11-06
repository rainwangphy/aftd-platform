import AFTD.Prelude

/-!
# loopless_digraph_count

Topic: graphs   Node: 8ff38218c2f0

Provenance: formalization of a published result. Source: arXiv:2611.02191 Sec. 1.1

For a degree sequence d on n vertices, D(d) is the number of loopless digraphs on n vertices in which every vertex v has both in-degree and out-degree equal to d(v).
-/

/-- The number D(d) of loopless digraphs on Fin n with in-degree and out-degree both equal to d. -/
noncomputable def loopless_digraph_count {n : ℕ} (d : Fin n → ℕ) : ℕ := open scoped Classical in open Finset in
  (univ.filter (fun D : Digraph (Fin n) =>
    (∀ v : Fin n, ¬ D.Adj v v) ∧
    (∀ v : Fin n, (univ.filter (fun w => D.Adj v w)).card = d v) ∧
    (∀ v : Fin n, (univ.filter (fun u => D.Adj u v)).card = d v))).card
