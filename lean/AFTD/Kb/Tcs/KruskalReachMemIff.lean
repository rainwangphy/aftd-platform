import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalReachMono

/-!
# Kruskal.reach_mem_iff

Topic: graphs   Node: 40231d611a6c

Provenance: helper lemma. TCSlib, `Kruskal.reach_mem_iff`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reachability depends only on the edge set. Fix $n \in \bbn$, and let $l_1$ and $l_2$ be two lists of weighted edges on the vertex
set $\mathrm{Fin}\,n$ that have the same members, i.e.\ $x \in l_1 \Leftrightarrow x \in
l_2$ for every weighted edge $x$. Then for any vertices $a, b \in \mathrm{Fin}\,n$, the
vertex $b$ is reachable from $a$ through the edges of $l_1$ if and only if it is
reachable from $a$ through the edges of $l_2$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.reach_mem_iff {n : ℕ} {l1 l2 : List (WEdge n)}
    (hmem : ∀ x, x ∈ l1 ↔ x ∈ l2) {a b : Fin n} :
    Reach l1 a b ↔ Reach l2 a b := by
  exact ⟨fun h => reach_mono h (fun e he => (hmem e).mp he),
         fun h => reach_mono h (fun e he => (hmem e).mpr he)⟩
