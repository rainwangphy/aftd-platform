import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUFFind
import AFTD.Kb.Tcs.KruskalUFInit

/-!
# Kruskal.UF.init_find

Topic: graphs   Node: cb46c7cd052f

Provenance: helper lemma. TCSlib, `Kruskal.UF.init_find`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Find on the initial union-find. Consider the identity union-find on $n$ nodes, in which every node is its own
representative. For every node $i \in \mathrm{Fin}\,n$, applying the find operation to
this initial state returns the underlying numeric value of $i$; that is, the
representative of $i$ is $i$ itself.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
@[simp] lemma Kruskal.UF.init_find {n : ℕ} (i : Fin n) : (init n).find i = i.val := rfl
