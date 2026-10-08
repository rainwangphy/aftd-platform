import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalSymAdj

/-!
# Kruskal.Reach

Topic: graphs   Node: f806b0100819

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.Reach`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{Reach}\,\mathit{edges}$ is the reflexive--transitive closure of
$\mathtt{SymAdj}\,\mathit{edges}$; that is, $\mathtt{Reach}\,\mathit{edges}\,u\,v$
holds when $u$ and $v$ are connected by a path through edges in $\mathit{edges}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.Reach {n : ℕ} (edges : List (WEdge n)) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (SymAdj edges)
