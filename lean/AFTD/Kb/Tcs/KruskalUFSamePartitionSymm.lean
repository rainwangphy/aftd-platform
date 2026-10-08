import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.UF.SamePartition.symm

Topic: graphs   Node: ce87e3bbef6e

Provenance: helper lemma. TCSlib, `Kruskal.UF.SamePartition.symm`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Symmetry of the same-partition relation. Fix $n \in \bbn$, and regard a union-find state on $n$ nodes as a function
$\mathrm{Fin}\,n \to \bbn$ assigning each node a representative. If two such states
$\mathit{uf}_1$ and $\mathit{uf}_2$ induce the same partition — that is, for all nodes
$i, j$ one has $\mathit{uf}_1(i) = \mathit{uf}_1(j)$ if and only if $\mathit{uf}_2(i) =
\mathit{uf}_2(j)$ — then $\mathit{uf}_2$ and $\mathit{uf}_1$ likewise induce the same
partition.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
@[symm] lemma Kruskal.UF.SamePartition.symm {n : ℕ} {uf1 uf2 : UF n}
    (h : UF.SamePartition uf1 uf2) : UF.SamePartition uf2 uf1 :=
  fun i j => (h i j).symm
