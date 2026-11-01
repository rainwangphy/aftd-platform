import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountAtThrough

/-!
# digraph_arborescence_count_at_through_root_eq_zero

Topic: graphs   Node: 78b17f3fa386

Provenance: helper lemma. step towards tournament_reverse_arc_arborescence_count_lt

The number of arborescences directed towards root r that use an arc starting at r is 0 whenever the target differs from r.
-/

/-- An arborescence directed towards root r cannot use an outgoing arc from r. -/
theorem digraph_arborescence_count_at_through_root_eq_zero {n : ℕ} (D : Digraph (Fin n))
    [DecidableRel D.Adj] (r b : Fin n) (hrb : r ≠ b) :
    digraph_arborescence_count_at_through D r r b = 0 := by
  rw [digraph_arborescence_count_at_through, Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact hrb (hp.1.symm.trans hp.2.2.2)
