import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.F

/-!
# Kruskal.SpansLike

Topic: graphs   Node: 53197b80af79

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.SpansLike`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{SpansLike}\,F\,E$ holds when the edge list $F$ is at least as connected as $E$:
for every pair of vertices $u, v$, if $u$ and $v$ are reachable in $E$ then they are
also reachable in $F$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.SpansLike {n : ℕ} (F E : List (WEdge n)) : Prop :=
  ∀ u v : Fin n, Reach E u v → Reach F u v
