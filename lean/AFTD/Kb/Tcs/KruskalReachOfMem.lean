import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach

/-!
# Kruskal.reach_of_mem

Topic: graphs   Node: 816c774fe093

Provenance: helper lemma. TCSlib, `Kruskal.reach_of_mem`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Endpoints of a listed edge are reachable. Let $\mathit{edges}$ be a list of weighted edges on $n$ vertices, and let $e$ be a
weighted edge belonging to $\mathit{edges}$. Then the endpoints $u$ and $v$ of $e$
satisfy $\mathtt{Reach}\,\mathit{edges}\,u\,v$; that is, they are connected by a path
through $\mathit{edges}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.reach_of_mem {n : ℕ} {edges : List (WEdge n)} {e : WEdge n}
    (he : e ∈ edges) : Reach edges e.u e.v :=
  Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
