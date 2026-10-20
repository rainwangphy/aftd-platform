import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountAt

/-!
# digraph_arborescence_count

Topic: graphs   Node: 78ef6ee9dc33

Provenance: formalization of a published result. Source: arXiv:2610.25886 (Extremal arborescences in graph orientations), Conjecture 6.1; tau(D) of Sec. 1

tau(D): the total number of arborescences of D, the sum of a_r(D) over all roots r.
-/

/-- tau(D): the total number of arborescences of D, the sum of a_r(D) over all roots r. -/
def digraph_arborescence_count {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj] : ℕ := ∑ r, digraph_arborescence_count_at D r
