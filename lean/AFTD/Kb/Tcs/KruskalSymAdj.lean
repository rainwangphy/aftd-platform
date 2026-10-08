import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge

/-!
# Kruskal.SymAdj

Topic: graphs   Node: 3a280c2b56db

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.SymAdj`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a list of weighted edges $\mathit{edges}$ on $n$ vertices, $\mathtt{SymAdj}\,\mathit{edges}\,u\,v$
holds when there exists an edge $e \in \mathit{edges}$ whose endpoints are $\{u, v\}$
(in either order), i.e.\ $(e.u = u \wedge e.v = v) \vee (e.u = v \wedge e.v = u)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.SymAdj {n : ℕ} (edges : List (WEdge n)) (u v : Fin n) : Prop :=
  ∃ e ∈ edges, (e.u = u ∧ e.v = v) ∨ (e.u = v ∧ e.v = u)
