import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.merge_noop

Topic: graphs   Node: 0b4f6ac3389c

Provenance: helper lemma. TCSlib, `Kruskal.merge_noop`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Merging within a single component leaves the state unchanged. Let $\mathit{uf}\colon \mathrm{Fin}\,n \to \bbn$ be a union-find state on $n$ nodes, and
let $i,j$ be two nodes whose representatives agree, $\mathit{uf}(i) = \mathit{uf}(j)$.
Then merging the components of $i$ and $j$ has no effect: the merged state equals
$\mathit{uf}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.merge_noop {n : ℕ} (uf : UF n) (i j : Fin n) (h : uf i = uf j) :
    uf.merge i j = uf := by
  funext k; unfold UF.merge; aesop
