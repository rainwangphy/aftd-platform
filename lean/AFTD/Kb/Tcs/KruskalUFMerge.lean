import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF

/-!
# Kruskal.UF.merge

Topic: graphs   Node: c604ee5255b5

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.UF.merge`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{merge}\,\mathit{uf}\,i\,j$ unifies the components of nodes $i$ and
$j$ by reassigning every node whose representative equals $\mathit{uf}(j)$ to
instead carry the representative $\mathit{uf}(i)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.UF.merge {n : ℕ} (uf : UF n) (i j : Fin n) : UF n :=
  let cj := uf j
  let ci := uf i
  fun k => if uf k = cj then ci else uf k
