import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalSymAdj

/-!
# Kruskal.symAdj_symm

Topic: graphs   Node: 51a730fad2ad

Provenance: helper lemma. TCSlib, `Kruskal.symAdj_symm`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Symmetry of symmetric adjacency. Fix a list of weighted edges on $n$ vertices, and let $u$ and $v$ be two vertices.
Recall that $u$ and $v$ are symmetrically adjacent when some edge in the list has $\{u,
v\}$ as its pair of endpoints, in either order. If $u$ and $v$ are symmetrically
adjacent, then so are $v$ and $u$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.symAdj_symm {n : ℕ} {edges : List (WEdge n)} {u v : Fin n}
    (h : SymAdj edges u v) : SymAdj edges v u :=
  h.imp fun _ he => ⟨he.1, he.2.symm⟩
