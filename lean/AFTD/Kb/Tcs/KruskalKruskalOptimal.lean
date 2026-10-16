import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalKruskal
import AFTD.Kb.Tcs.KruskalProcessEdgesOptimal
import AFTD.Kb.Tcs.KruskalSpansLike
import AFTD.Kb.Tcs.KruskalReachMono
import AFTD.Kb.Tcs.KruskalTotalWeight
import AFTD.Kb.Tcs.KruskalMergeAllInitIff
import AFTD.Kb.Tcs.KruskalUFInitFind
import AFTD.Kb.Tcs.KruskalUFFindDef
import AFTD.Kb.Tcs.KruskalTotalWeightNil
import AFTD.Kb.Tcs.KruskalUFMergeAll
import AFTD.Kb.Tcs.KruskalUFInit
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalSymAdj

/-!
# Kruskal.kruskal_optimal

Topic: graphs   Node: 464186d2abb5

Provenance: formalization of a published result. Source: Optimality of Kruskal's algorithm, as formalized in TCSlib (`Kruskal.kruskal_optimal`). Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Optimality.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Optimality of Kruskal's algorithm. Let $E$ be a list of weighted edges on $n$ vertices, and let $S$ be another such list in
which every edge is also an edge of $E$. Suppose that $S$ spans like $E$: whenever two
vertices $u$ and $v$ are joined by a path through the edges of $E$, they are also joined
by a path through the edges of $S$. Let $K$ denote the edge list produced by Kruskal's
algorithm on $E$, and write $w(e)$ for the weight of an edge $e$. Then the total weight
of $K$ is no greater than that of $S$:
\[
  \sum_{e \in K} w(e) \;\le\; \sum_{e \in S} w(e).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
theorem Kruskal.kruskal_optimal {n : ℕ} (E S : List (WEdge n))
    (hSsub : ∀ e ∈ S, e ∈ E) (hSspan : SpansLike S E) :
    totalWeight (kruskal n E) ≤ totalWeight S := by
  refine processEdges_optimal _ _ [] ?_ S ?_ ?_ ?_
  · intro a b
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases Fin.ext h; exact Relation.ReflTransGen.refl
    · induction h with
      | refl => rfl
      | tail _ hcd _ => obtain ⟨_, h, _⟩ := hcd; cases h
  · exact fun e he => List.mem_mergeSort.mpr (hSsub e he)
  · intro a b
    rw [mergeAll_init_iff, mergeAll_init_iff]
    refine ⟨fun h => reach_mono h fun e he => List.mem_mergeSort.mpr (hSsub e he),
      fun h => hSspan a b <| reach_mono h fun e he => List.mem_mergeSort.mp he⟩
  · have h := List.pairwise_mergeSort
      (le := fun e₁ e₂ : WEdge n => decide (e₁.weight ≤ e₂.weight))
      (by intro a b c; simp; exact le_trans) (by intro a b; simp; exact le_total _ _) E
    exact h.imp (by intro a b h; simpa using h)
