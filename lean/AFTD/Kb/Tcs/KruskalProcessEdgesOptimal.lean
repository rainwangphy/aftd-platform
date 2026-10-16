import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFFind
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalUFMergeAll
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalProcessEdges
import AFTD.Kb.Tcs.KruskalReduceToRest
import AFTD.Kb.Tcs.KruskalUfExchange
import AFTD.Kb.Tcs.KruskalProcessEdgesSkip
import AFTD.Kb.Tcs.KruskalProcessEdgesTakeWeight
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalTotalWeight
import AFTD.Kb.Tcs.KruskalTotalWeightErase
import AFTD.Kb.Tcs.KruskalUFSamePartitionSymm
import AFTD.Kb.Tcs.KruskalUFSamePartitionTrans
import AFTD.Kb.Tcs.KruskalEraseAppendPerm
import AFTD.Kb.Tcs.KruskalMergeAllConsEq
import AFTD.Kb.Tcs.KruskalMergeAllIffReach
import AFTD.Kb.Tcs.KruskalMergeAllPerm
import AFTD.Kb.Tcs.KruskalMergeNoop
import AFTD.Kb.Tcs.KruskalUFFindDef
import AFTD.Kb.Tcs.KruskalTotalWeightNil
import AFTD.Kb.Tcs.KruskalSymAdj
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Kruskal.processEdges_optimal

Topic: graphs   Node: 7e29a63061b2

Provenance: helper lemma. TCSlib, `Kruskal.processEdges_optimal`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Optimality.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Optimality of the greedy edge-selection sweep. Let $\mathit{edges}$ be a list of weighted edges on $n$ vertices, sorted in
nondecreasing order of weight, and let $\mathit{uf}$ be a union-find state whose induced
partition is exactly the reachability relation of some base edge list $\mathit{base}$:
for all vertices $a$ and $b$, the representatives $\mathit{uf}(a)$ and $\mathit{uf}(b)$
are equal if and only if $a$ and $b$ are joined by a path through the edges of
$\mathit{base}$. Let $S$ be any list of edges, each of which occurs in $\mathit{edges}$,
such that merging all of $S$ into $\mathit{uf}$ and merging all of $\mathit{edges}$ into
$\mathit{uf}$ yield the same partition of the vertices. Then the greedy sweep — which
starts from $\mathit{uf}$, scans $\mathit{edges}$ in order, and keeps each edge exactly
when its two endpoints lie in currently distinct components — produces a set of edges
whose total weight is at most the total weight of $S$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.processEdges_optimal {n : ℕ}
    (edges : List (WEdge n)) (uf : UF n) (base : List (WEdge n))
    (huf : ∀ a b : Fin n, uf a = uf b ↔ Reach base a b)
    (S : List (WEdge n)) (hSsub : ∀ e ∈ S, e ∈ edges)
    (hSspan : UF.SamePartition (uf.mergeAll S) (uf.mergeAll edges))
    (hsorted : List.Pairwise (fun e1 e2 => e1.weight ≤ e2.weight) edges) :
    totalWeight (processEdges edges uf []) ≤ totalWeight S := by
  induction' edges with e edges ih generalizing uf base S
  · simp [processEdges, totalWeight]
  · by_cases he : uf.find e.u = uf.find e.v
    · obtain ⟨S', hS'sub, hS'span, hS'weight⟩ :
          ∃ S', (∀ e ∈ S', e ∈ edges) ∧
            (uf.mergeAll S').SamePartition (uf.mergeAll edges) ∧
            totalWeight S' ≤ totalWeight S := by
        apply reduce_to_rest
        · exact hSsub
        · convert hSspan.trans _ using 1
          convert mergeAll_cons_eq uf e edges using 1
          rw [merge_noop]; aesop
        · exact he
      rw [processEdges_skip he]
      exact le_trans (ih uf base huf S' hS'sub hS'span
        ((List.pairwise_cons.mp hsorted).2)) hS'weight
    · by_cases heS : e ∈ S <;> simp_all +decide [processEdges_take_weight]
      · have hS'_subset : UF.SamePartition
            ((uf.merge e.u e.v).mergeAll (S.erase e))
            ((uf.merge e.u e.v).mergeAll edges) := by
          have hp1 : UF.SamePartition (uf.mergeAll (S.erase e ++ [e]))
              (uf.mergeAll (e :: edges)) :=
            (mergeAll_perm uf (erase_append_perm heS).symm).trans hSspan
          have hp2 : UF.SamePartition ((uf.merge e.u e.v).mergeAll (S.erase e))
              (uf.mergeAll (S.erase e ++ [e])) :=
            (by convert mergeAll_perm uf (show List.Perm (S.erase e ++ [e])
                (e :: S.erase e) from by grind) using 1 <;> try rfl :
              UF.SamePartition (uf.mergeAll (S.erase e ++ [e]))
                ((uf.merge e.u e.v).mergeAll (S.erase e))).symm
          convert hp2.trans ‹_› using 1 <;> try rfl
        obtain ⟨S', hS'_subset, hS'_span, hS'_weight⟩ :=
          reduce_to_rest (uf.merge e.u e.v) e edges (S.erase e)
            (by grind) hS'_subset (by simp [UF.merge])
        have := ih (uf.merge e.u e.v) (base ++ [e])
          (by intros a b
              exact mergeAll_iff_reach uf base [e] huf a b)
          S' hS'_subset hS'_span
        linarith [totalWeight_erase S e heS, processEdges_take_weight (e := e) (rest := edges) (uf := uf)
          (fun h => he ((huf _ _).1 h))]
      · obtain ⟨f, hfS, hf⟩ : ∃ f ∈ S, UF.SamePartition
            ((uf.merge e.u e.v).mergeAll (S.erase f)) (uf.mergeAll S) := by
          apply uf_exchange
          · exact huf
          · exact (hSspan _ _).2 ((mergeAll_iff_reach uf base (e :: edges) huf _ _).2
              (Relation.ReflTransGen.single (by exact ⟨e, by aesop⟩)))
          · exact fun h => he <| (huf _ _).1 h
        obtain ⟨S', hS'sub, hS'span, hS'weight⟩ : ∃ S' : List (WEdge n),
            (∀ x ∈ S', x ∈ edges) ∧
            UF.SamePartition ((uf.merge e.u e.v).mergeAll S')
              ((uf.merge e.u e.v).mergeAll edges) ∧
            totalWeight S' ≤ totalWeight (S.erase f) := by
          apply reduce_to_rest
          any_goals exact e
          · grind
          · refine hf.trans ?_; convert hSspan using 1 <;> try rfl
          · unfold UF.merge; aesop
        have := ih (uf.merge e.u e.v) (base ++ [e])
          (mergeAll_iff_reach uf base [e] huf) S' hS'sub hS'span
        have hfedges : f ∈ edges := by
          rcases hSsub f hfS with rfl | h
          · exact absurd hfS heS
          · exact h
        linarith [totalWeight_erase S f hfS, hsorted.1 f hfedges, processEdges_take_weight (e := e) (rest := edges) (uf := uf)
          (fun h => he ((huf _ _).1 h))]
