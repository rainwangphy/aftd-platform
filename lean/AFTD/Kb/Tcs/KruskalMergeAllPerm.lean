import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFMergeAll
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalUFSamePartitionTrans
import AFTD.Kb.Tcs.KruskalMergeAllCongr
import AFTD.Kb.Tcs.KruskalMergeSwapPartition
import AFTD.Kb.Tcs.KruskalUFFindDef
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalUFSamePartitionRfl

/-!
# Kruskal.mergeAll_perm

Topic: graphs   Node: 48d61e3bf470

Provenance: helper lemma. TCSlib, `Kruskal.mergeAll_perm`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Permutation invariance of edge merging. Fix $n$ and an initial union-find state $\mathit{uf} : \mathrm{Fin}\,n \to \bbn$. If two
lists of weighted edges $l_1$ and $l_2$ over $n$ vertices are permutations of one
another, then folding each list into $\mathit{uf}$ by merging the endpoints of every
edge in turn yields two union-find states that induce the same partition of the nodes;
that is, for all $i, j : \mathrm{Fin}\,n$, the two states assign $i$ and $j$ equal
representatives under one exactly when they do under the other.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.mergeAll_perm {n : ℕ} (uf : UF n) {l1 l2 : List (WEdge n)}
    (hp : l1.Perm l2) :
    UF.SamePartition (uf.mergeAll l1) (uf.mergeAll l2) := by
  induction hp generalizing uf with
  | nil => rfl
  | cons _ _ ih => exact ih _
  | swap a b _ => exact mergeAll_congr _ (merge_swap_partition uf b a)
  | trans _ _ ih1 ih2 => exact (ih1 _).trans (ih2 _)
