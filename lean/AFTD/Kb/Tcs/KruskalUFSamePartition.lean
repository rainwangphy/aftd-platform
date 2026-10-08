import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.UF.SamePartition

Topic: graphs   Node: b78012ca4316

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.UF.SamePartition`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{SamePartition}\,\mathit{uf}_1\,\mathit{uf}_2$ holds when two
union-find states induce the same equivalence relation on nodes: for all
$i, j : \mathrm{Fin}\,n$, $\mathit{uf}_1(i) = \mathit{uf}_1(j)$ if and
only if $\mathit{uf}_2(i) = \mathit{uf}_2(j)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.UF.SamePartition {n : ℕ} (uf1 uf2 : UF n) : Prop :=
  ∀ i j : Fin n, uf1 i = uf1 j ↔ uf2 i = uf2 j
