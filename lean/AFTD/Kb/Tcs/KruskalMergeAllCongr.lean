import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalUFMergeAll
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.mergeAll_congr

Topic: graphs   Node: 3b64ebcf3307

Provenance: helper lemma. TCSlib, `Kruskal.mergeAll_congr`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Merging edges preserves equal partitions. Let $\mathit{uf}_1, \mathit{uf}_2 : \mathrm{Fin}\,n \to \bbn$ be two union-find states
over $n$ nodes that induce the same partition, meaning that for all nodes $i, j$ one has
$\mathit{uf}_1(i) = \mathit{uf}_1(j)$ if and only if $\mathit{uf}_2(i) =
\mathit{uf}_2(j)$. Then for any list of weighted edges, folding that list into each
state by successively merging the endpoints of every edge yields two states that again
induce the same partition.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.mergeAll_congr {n : ℕ} {uf1 uf2 : UF n} (edges : List (WEdge n))
    (h : UF.SamePartition uf1 uf2) :
    UF.SamePartition (uf1.mergeAll edges) (uf2.mergeAll edges) := by
  unfold UF.SamePartition at h ⊢
  induction edges generalizing uf1 uf2 with
  | nil => exact h
  | cons e edges ih =>
    refine ih (uf1 := uf1.merge e.u e.v) (uf2 := uf2.merge e.u e.v) ?_
    intro i j; unfold UF.merge; grind
