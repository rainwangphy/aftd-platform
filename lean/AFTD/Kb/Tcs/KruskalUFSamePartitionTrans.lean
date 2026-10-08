import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.UF.SamePartition.trans

Topic: graphs   Node: 1246ee7e2322

Provenance: helper lemma. TCSlib, `Kruskal.UF.SamePartition.trans`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Transitivity of the same-partition relation. Let $n$ be a natural number, and let $\mathit{uf}_1, \mathit{uf}_2, \mathit{uf}_3 :
\mathrm{Fin}\,n \to \bbn$ be three union-find states on $n$ nodes. Suppose that
$\mathit{uf}_1$ and $\mathit{uf}_2$ induce the same partition of the nodes, and that
$\mathit{uf}_2$ and $\mathit{uf}_3$ induce the same partition. Then $\mathit{uf}_1$ and
$\mathit{uf}_3$ induce the same partition: for all nodes $i, j$, one has
$\mathit{uf}_1(i) = \mathit{uf}_1(j)$ if and only if $\mathit{uf}_3(i) =
\mathit{uf}_3(j)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
@[trans] lemma Kruskal.UF.SamePartition.trans {n : ℕ} {uf1 uf2 uf3 : UF n}
    (h1 : UF.SamePartition uf1 uf2) (h2 : UF.SamePartition uf2 uf3) :
    UF.SamePartition uf1 uf3 :=
  fun i j => (h1 i j).trans (h2 i j)
