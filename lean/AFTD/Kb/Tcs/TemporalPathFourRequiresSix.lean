import AFTD.Prelude
import AFTD.Kb.Tcs.IsTemporalWalk
import AFTD.Kb.Tcs.IsSpanningPathGraph
import AFTD.Kb.Tcs.TemporalWalkExploresBy

/-!
# temporal_path_four_requires_six

Topic: graphs   Node: a31e8e0a5c74

Provenance: original. Related work: OP-80, arXiv:2610.06228 Sec. 7 (path snapshots). An explicit finite obstruction computed in the deep session; this is a small case, not an asymptotic advance.

There is a temporal graph on four vertices with spanning-path snapshots such that every temporal walk starting at vertex 0 needs at least six steps to visit all four vertices.
-/

private def fourOrder (t : ℕ) : Equiv.Perm (Fin 4) :=
  match t with
  | 0 => Equiv.refl _
  | 1 => Equiv.swap 0 1
  | 2 => (Equiv.swap 1 2).trans (Equiv.swap 0 1)
  | _ => Equiv.swap 0 2

private def fourGraph (t : ℕ) : SimpleGraph (Fin 4) :=
  (SimpleGraph.pathGraph 4).comap (fourOrder t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fourCertificate :
    ∀ v : Fin 6 → Fin 4, v 0 = 0 →
      (∀ i : Fin 5, v i.succ = v i.castSucc ∨
        (fourGraph i.val).Adj (v i.castSucc) (v i.succ)) →
      ¬ (∀ a : Fin 4, ∃ i : Fin 6, v i = a) := by
  simp only [fourGraph, SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
  decide

theorem temporal_path_four_requires_six :
    ∃ G : ℕ → SimpleGraph (Fin 4),
      (∀ t, is_spanning_path_graph (G t)) ∧
      ∀ w : ℕ → Fin 4, w 0 = 0 → is_temporal_walk G w →
        ¬ temporal_walk_explores_by w 5 := by
  refine ⟨fourGraph, ?_, ?_⟩
  · intro t
    exact ⟨fourOrder t, fun a b => SimpleGraph.pathGraph_adj⟩
  · intro w hw0 hw hex
    apply fourCertificate (fun i => w i.val) hw0
    · intro i
      exact hw i.val
    · intro a
      obtain ⟨t, ht, he⟩ := hex a
      exact ⟨⟨t, by omega⟩, he⟩
