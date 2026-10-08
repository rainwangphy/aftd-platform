import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFFind

/-!
# Kruskal.UF.find_def

Topic: graphs   Node: 7f0f2a5a66c4

Provenance: helper lemma. TCSlib, `Kruskal.UF.find_def`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Find equals direct lookup. Let $\mathit{uf} \colon \mathrm{Fin}\,n \to \bbn$ be a union-find state on $n$ nodes,
and let $i$ be one of its nodes. Then the representative of $i$ returned by
$\mathrm{find}$ coincides with the direct evaluation of the state at $i$; that is,
$\mathrm{find}(\mathit{uf}, i) = \mathit{uf}(i)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
@[simp] lemma Kruskal.UF.find_def {n : ℕ} (uf : UF n) (i : Fin n) : uf.find i = uf i := rfl
