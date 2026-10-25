import AFTD.Prelude
import AFTD.Kb.Tcs.TemporalTargetStateTableSound
import AFTD.Kb.Tcs.IsSpanningPathGraph
import AFTD.Kb.Tcs.IsTemporalWalk
import AFTD.Kb.Tcs.TemporalWalkExploresBy

/-!
# temporal_path_five_requires_nine

Topic: graphs   Node: c8edfffc7b5a

Provenance: original. Related work: OP-80, arXiv:2610.06228 Sec. 7. An explicit finite obstruction from this deep session; no asymptotic advance is claimed.

There is a temporal graph on five vertices with spanning-path snapshots such that every walk from vertex 0 needs at least nine steps to visit all vertices.
-/

private def fiveOrder (t : ℕ) : Equiv.Perm (Fin 5) :=
  match t with
  | 0 | 2 => ((Equiv.swap 1 4).trans (Equiv.swap 2 1)).trans (Equiv.swap 3 2)
  | 1 => ((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 3 4)
  | 3 | 4 => ((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 0 1)
  | 5 => Equiv.swap 2 3
  | _ => (Equiv.swap 0 2).trans (Equiv.swap 0 3)

private def fiveGraph (t : ℕ) : SimpleGraph (Fin 5) :=
  (SimpleGraph.pathGraph 5).comap (fiveOrder t)

private instance fiveGraphDec (t : ℕ) : DecidableRel (fiveGraph t).Adj :=
  fun a b => decidable_of_iff
    (((fiveOrder t a : Fin 5) : ℕ) + 1 = fiveOrder t b ∨
      ((fiveOrder t b : Fin 5) : ℕ) + 1 = fiveOrder t a)
    SimpleGraph.pathGraph_adj.symm


private def fiveTable : ℕ → Finset (Fin 5 × Finset (Fin 5))
  | 0 => {(0, {0})}
  | 1 => {(0, {0}), (2, {0, 2})}
  | 2 => {(0, {0}), (0, {0, 2}), (1, {0, 1}), (2, {0, 2})}
  | 3 => {(0, {0}), (0, {0, 2}), (1, {0, 1}), (2, {0, 2}), (3, {0, 2, 3}), (4, {0, 1, 4})}
  | 4 => {(0, {0}), (0, {0, 1}), (0, {0, 2}), (1, {0, 1}), (1, {0, 1, 2}), (1, {0, 1, 4}), (2, {0, 2}), (2, {0, 2, 3}), (3, {0, 2, 3}), (4, {0, 1, 4})}
  | 5 => {(0, {0}), (0, {0, 1}), (0, {0, 1, 2}), (0, {0, 1, 4}), (0, {0, 2}), (0, {0, 2, 3}), (1, {0, 1}), (1, {0, 1, 2}), (1, {0, 1, 4}), (2, {0, 1, 2}), (2, {0, 2}), (2, {0, 2, 3}), (3, {0, 2, 3}), (4, {0, 1, 2, 4}), (4, {0, 1, 4})}
  | 6 => {(0, {0}), (0, {0, 1}), (0, {0, 1, 2}), (0, {0, 1, 4}), (0, {0, 2}), (0, {0, 2, 3}), (1, {0, 1}), (1, {0, 1, 2}), (1, {0, 1, 2, 3}), (1, {0, 1, 4}), (2, {0, 1, 2}), (2, {0, 1, 2, 4}), (2, {0, 2}), (2, {0, 2, 3}), (3, {0, 1, 2, 3}), (3, {0, 1, 3}), (3, {0, 1, 3, 4}), (3, {0, 2, 3}), (4, {0, 1, 2, 4}), (4, {0, 1, 4}), (4, {0, 2, 3, 4}), (4, {0, 2, 4})}
  | 7 => {(0, {0}), (0, {0, 1}), (0, {0, 1, 2}), (0, {0, 1, 2, 3}), (0, {0, 1, 2, 4}), (0, {0, 1, 4}), (0, {0, 2}), (0, {0, 2, 3}), (1, {0, 1}), (1, {0, 1, 2}), (1, {0, 1, 2, 3}), (1, {0, 1, 3}), (1, {0, 1, 3, 4}), (1, {0, 1, 4}), (2, {0, 1, 2}), (2, {0, 1, 2, 4}), (2, {0, 2}), (2, {0, 2, 3}), (2, {0, 2, 3, 4}), (2, {0, 2, 4}), (3, {0, 1, 2, 3}), (3, {0, 1, 3}), (3, {0, 1, 3, 4}), (3, {0, 2, 3}), (4, {0, 1, 2, 4}), (4, {0, 1, 4}), (4, {0, 2, 3, 4}), (4, {0, 2, 4})}
  | 8 => {(0, {0}), (0, {0, 1}), (0, {0, 1, 2}), (0, {0, 1, 2, 3}), (0, {0, 1, 2, 4}), (0, {0, 1, 3}), (0, {0, 1, 3, 4}), (0, {0, 1, 4}), (0, {0, 2}), (0, {0, 2, 3}), (0, {0, 2, 3, 4}), (0, {0, 2, 4}), (1, {0, 1}), (1, {0, 1, 2}), (1, {0, 1, 2, 3}), (1, {0, 1, 2, 4}), (1, {0, 1, 3}), (1, {0, 1, 3, 4}), (1, {0, 1, 4}), (2, {0, 1, 2}), (2, {0, 1, 2, 3}), (2, {0, 1, 2, 4}), (2, {0, 2}), (2, {0, 2, 3}), (2, {0, 2, 3, 4}), (2, {0, 2, 4}), (3, {0, 1, 2, 3}), (3, {0, 1, 3}), (3, {0, 1, 3, 4}), (3, {0, 2, 3}), (4, {0, 1, 2, 4}), (4, {0, 1, 4}), (4, {0, 2, 3, 4}), (4, {0, 2, 4})}
  | _ => ∅

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
private theorem fiveClosed :
    ∀ t : Fin 8, ∀ p ∈ fiveTable t.val, ∀ u : Fin 5,
      u = p.1 ∨ (fiveGraph t.val).Adj p.1 u →
      (u, if u ∈ Finset.univ then insert u p.2 else p.2) ∈ fiveTable (t.val + 1) := by
  intro t
  fin_cases t <;>
    simp only [fiveTable, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq] <;>
    simp only [fiveGraph, SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj] <;>
    (repeat' apply And.intro) <;>
    decide



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
private theorem fiveCard :
    ∀ p ∈ fiveTable 8, p.2.card ≤ 4 := by
  simp only [fiveTable, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  decide

theorem temporal_path_five_requires_nine :
    ∃ G : ℕ → SimpleGraph (Fin 5),
      (∀ t, is_spanning_path_graph (G t)) ∧
      ∀ w : ℕ → Fin 5, w 0 = 0 → is_temporal_walk G w →
        ¬ temporal_walk_explores_by w 8 := by
  refine ⟨fiveGraph, ?_, ?_⟩
  · intro t
    exact ⟨fiveOrder t, fun a b => SimpleGraph.pathGraph_adj⟩
  · intro w hw0 hw hex
    obtain ⟨M, hM, hcover⟩ :=
      temporal_target_state_table_sound fiveGraph Finset.univ 0 8 fiveTable {0} (by decide) (by simp) fiveClosed w hw0 hw
    have hcard := fiveCard (w 8, M) hM
    change M.card ≤ 4 at hcard
    have hfull : Finset.univ ⊆ M := by
      intro a ha
      obtain ⟨t, ht, he⟩ := hex a
      rw [← he]
      exact hcover t ht (Finset.mem_univ _)
    have hge := Finset.card_le_card hfull
    simp only [Finset.card_univ, Fintype.card_fin] at hge
    omega
