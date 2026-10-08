import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalSymAdjMono

/-!
# Kruskal.reach_mono

Topic: graphs   Node: 67e942fe99ac

Provenance: helper lemma. TCSlib, `Kruskal.reach_mono`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Monotonicity of reachability under edge addition. Fix $n$, let $e_1$ and $e_2$ be lists of weighted edges on the vertex set
$\mathrm{Fin}\,n$, and let $u, v : \mathrm{Fin}\,n$. Suppose $u$ and $v$ are connected
by a path through the edges of $e_1$, and that every edge of $e_1$ also occurs in $e_2$.
Then $u$ and $v$ are connected by a path through the edges of $e_2$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.reach_mono {n : ℕ} {e1 e2 : List (WEdge n)} {u v : Fin n}
    (h : Reach e1 u v) (hs : ∀ e ∈ e1, e ∈ e2) : Reach e2 u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih => exact ih.tail (symAdj_mono hcd hs)
