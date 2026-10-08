import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.UF.SamePartition.rfl

Topic: graphs   Node: 25f5b8cd4ad8

Provenance: helper lemma. TCSlib, `Kruskal.UF.SamePartition.rfl`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reflexivity of the same-partition relation. Fix $n \in \bbn$, and recall that a union-find state on $n$ nodes is a function
$\mathrm{Fin}\,n \to \bbn$ assigning to each node a representative label. Every such
state $\mathit{uf}$ induces the same partition as itself: for all nodes $i, j :
\mathrm{Fin}\,n$, one has $\mathit{uf}(i) = \mathit{uf}(j)$ if and only if
$\mathit{uf}(i) = \mathit{uf}(j)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
@[refl] lemma Kruskal.UF.SamePartition.rfl {n : ℕ} (uf : UF n) : UF.SamePartition uf uf :=
  fun _ _ => Iff.rfl
