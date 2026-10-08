import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF

/-!
# Kruskal.UF.find

Topic: graphs   Node: 305fdc30e801

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.UF.find`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{find}\,\mathit{uf}\,i$ returns the representative of node $i$ in
the union-find state $\mathit{uf}$, defined simply as $\mathit{uf}(i)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.UF.find {n : ℕ} (uf : UF n) (i : Fin n) : ℕ := uf i
