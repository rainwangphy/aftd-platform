import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalSymAdj

/-!
# Kruskal.symAdj_mono

Topic: graphs   Node: 1f75a761fcc7

Provenance: helper lemma. TCSlib, `Kruskal.symAdj_mono`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Monotonicity of symmetric adjacency. Fix $n \in \bbn$ and two vertices $u, v \in \mathrm{Fin}\,n$, and let $e_1$ and $e_2$ be
lists of weighted edges on $n$ vertices such that every edge of $e_1$ also occurs in
$e_2$. If $u$ and $v$ are symmetrically adjacent in $e_1$ — that is, some edge of $e_1$
has endpoints $\{u,v\}$ in either order — then $u$ and $v$ are symmetrically adjacent in
$e_2$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.symAdj_mono {n : ℕ} {e1 e2 : List (WEdge n)} {u v : Fin n}
    (h : SymAdj e1 u v) (hs : ∀ e ∈ e1, e ∈ e2) : SymAdj e2 u v :=
  h.imp fun _ he => ⟨hs _ he.1, he.2⟩
