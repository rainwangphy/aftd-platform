import AFTD.Prelude
import AFTD.Kb.Tcs.MinorEdgeIsLoop

/-!
# minor_edge_not_loop_of_all_none

Topic: graphs   Node: 7f228fd4071a

Provenance: helper lemma. folklore

Sanity check: if no edge has been queried (every edge is assigned weight none), then no edge of G is a loop in the minor G_β.
-/

/-- Sanity check: when no edges are queried, no edge is a loop in the minor. -/
theorem minor_edge_not_loop_of_all_none {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) :
    ¬ minor_edge_is_loop G (fun _ => none) e := by
  intro h
  unfold minor_edge_is_loop at h
  rcases h with ⟨u, v, he, ⟨w⟩⟩
  induction w with
  | nil =>
    have hd : (e : Sym2 V).IsDiag := by
      rw [he]
      exact Sym2.mk_isDiag_iff.mpr rfl
    exact G.not_mem_edgeSet_of_isDiag hd e.2
  | cons hadj _ _ =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    rcases hadj.1 with ⟨_, h_none⟩
    contradiction
