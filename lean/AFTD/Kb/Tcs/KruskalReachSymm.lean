import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalSymAdjSymm

/-!
# Kruskal.reach_symm

Topic: graphs   Node: a45b176657b0

Provenance: helper lemma. TCSlib, `Kruskal.reach_symm`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Symmetry of reachability. Let $\mathit{edges}$ be a list of weighted edges on $n$ vertices, and call two vertices
reachable when they are joined by a path along these edges (in the sense of the
reflexive–transitive closure of symmetric adjacency). Then reachability is symmetric:
for all vertices $u, v$, if $u$ is reachable from $v$, then $v$ is reachable from $u$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.reach_symm {n : ℕ} {edges : List (WEdge n)} {u v : Fin n}
    (h : Reach edges u v) : Reach edges v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih =>
    exact (Relation.ReflTransGen.single (symAdj_symm hcd)).trans ih
