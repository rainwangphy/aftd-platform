import AFTD.Prelude
import AFTD.Kb.Tcs.TemporalTargetStateTableSound
import AFTD.Kb.Tcs.IsSpanningPathGraph
import AFTD.Kb.Tcs.IsTemporalWalk

/-!
# temporal_path_twelve_one_frame_target_trap

Topic: graphs   Node: 2d38f79765c6

Provenance: original. Related work: OP-80, arXiv:2610.06228 Sec. 7. An explicit finite obstruction from this deep session; no asymptotic advance is claimed.

There is a temporal graph on twelve vertices, every snapshot a spanning path, such that every walk from vertex 0 visits at most one of the four designated targets 8, 9, 10, 11 by time 11. This refutes the auxiliary one-frame half-target-coverage lemma from a prescribed start; it does not refute OP-80.
-/

private def twelveOrder (t : ℕ) : Equiv.Perm (Fin 12) :=
  if t < 8 then Equiv.refl _
  else if t < 9 then Equiv.swap 0 8
  else if t < 10 then (Equiv.swap 0 8).trans (Equiv.swap 4 9)
  else ((Equiv.swap 0 8).trans (Equiv.swap 4 9)).trans (Equiv.swap 7 10)

private def twelveGraph (t : ℕ) : SimpleGraph (Fin 12) :=
  (SimpleGraph.pathGraph 12).comap (twelveOrder t)

private instance twelveGraphDec (t : ℕ) : DecidableRel (twelveGraph t).Adj :=
  fun a b => decidable_of_iff
    (((twelveOrder t a : Fin 12) : ℕ) + 1 = twelveOrder t b ∨
      ((twelveOrder t b : Fin 12) : ℕ) + 1 = twelveOrder t a)
    SimpleGraph.pathGraph_adj.symm

private def twelveTargets : Finset (Fin 12) :=
  Finset.univ.filter fun v => 8 ≤ v.val


private def twelveTable : ℕ → Finset (Fin 12 × Finset (Fin 12))
  | 0 => {(0, ∅)}
  | 1 => {(0, ∅), (1, ∅)}
  | 2 => {(0, ∅), (1, ∅), (2, ∅)}
  | 3 => {(0, ∅), (1, ∅), (2, ∅), (3, ∅)}
  | 4 => {(0, ∅), (1, ∅), (2, ∅), (3, ∅), (4, ∅)}
  | 5 => {(0, ∅), (1, ∅), (2, ∅), (3, ∅), (4, ∅), (5, ∅)}
  | 6 => {(0, ∅), (1, ∅), (2, ∅), (3, ∅), (4, ∅), (5, ∅), (6, ∅)}
  | 7 => {(0, ∅), (1, ∅), (2, ∅), (3, ∅), (4, ∅), (5, ∅), (6, ∅), (7, ∅)}
  | 8 => {(0, ∅), (1, ∅), (2, ∅), (3, ∅), (4, ∅), (5, ∅), (6, ∅), (7, ∅), (8, {8})}
  | 9 => {(0, ∅), (1, ∅), (1, {8}), (2, ∅), (3, ∅), (4, ∅), (5, ∅), (6, ∅), (7, ∅), (8, {8}), (9, {9})}
  | 10 => {(0, ∅), (1, ∅), (1, {8}), (2, ∅), (2, {8}), (3, ∅), (3, {9}), (4, ∅), (5, ∅), (5, {9}), (6, ∅), (7, ∅), (8, {8}), (9, {9}), (10, {10})}
  | 11 => {(0, ∅), (0, {10}), (1, ∅), (1, {8}), (2, ∅), (2, {8}), (2, {9}), (3, ∅), (3, {8}), (3, {9}), (4, ∅), (5, ∅), (5, {9}), (6, ∅), (6, {9}), (6, {10}), (7, ∅), (8, {8}), (9, {9}), (10, {10}), (11, {11})}
  | _ => ∅

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
private theorem twelveClosed :
    ∀ t : Fin 11, ∀ p ∈ twelveTable t.val, ∀ u : Fin 12,
      u = p.1 ∨ (twelveGraph t.val).Adj p.1 u →
      (u, if u ∈ twelveTargets then insert u p.2 else p.2) ∈ twelveTable (t.val + 1) := by
  intro t
  fin_cases t <;>
    simp only [twelveTable, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq] <;>
    simp only [twelveGraph, SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj] <;>
    (repeat' apply And.intro) <;>
    decide



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
private theorem twelveCard :
    ∀ p ∈ twelveTable 11, p.2.card ≤ 1 := by
  simp only [twelveTable, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  decide

theorem temporal_path_twelve_one_frame_target_trap :
    ∃ G : ℕ → SimpleGraph (Fin 12),
      (∀ t, is_spanning_path_graph (G t)) ∧
      ∀ w : ℕ → Fin 12, w 0 = 0 → is_temporal_walk G w →
        ∃ M : Finset (Fin 12), M.card ≤ 1 ∧
          ∀ i ≤ 11, 8 ≤ (w i).val → w i ∈ M := by
  refine ⟨twelveGraph, ?_, ?_⟩
  · intro t
    exact ⟨twelveOrder t, fun a b => SimpleGraph.pathGraph_adj⟩
  · intro w hw0 hw
    obtain ⟨M, hM, hcover⟩ :=
      temporal_target_state_table_sound twelveGraph twelveTargets 0 11 twelveTable ∅ (by decide) (by decide) twelveClosed w hw0 hw
    refine ⟨M, twelveCard (w 11, M) hM, ?_⟩
    intro i hi hui
    exact hcover i hi (by simpa [twelveTargets] using hui)
