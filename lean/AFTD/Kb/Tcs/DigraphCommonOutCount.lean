import AFTD.Prelude

/-!
# digraph_common_out_count

Topic: graphs   Node: 2e4139fb4ffe

Provenance: formalization of a published result. Source: arXiv:2610.25886 (Extremal arborescences in graph orientations), Conjecture 6.1; the counts c_ij of Sec. 6

c_ij: the number of common out-neighbours of the vertices i and j of a digraph on Fin n.
-/

/-- c_ij: the number of common out-neighbours of the vertices i and j of a digraph on Fin n. -/
def digraph_common_out_count {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj]
    (i j : Fin n) : ℕ :=
  (Finset.univ.filter (fun v => D.Adj i v ∧ D.Adj j v)).card
