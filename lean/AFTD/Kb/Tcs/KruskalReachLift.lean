import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalSymAdj

/-!
# Kruskal.reach_lift

Topic: graphs   Node: f3607f2b328a

Provenance: helper lemma. TCSlib, `Kruskal.reach_lift`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lifting reachability along an edge set. Let $\mathit{edges}$ and $\mathit{edges}'$ be two lists of weighted edges on $n$
vertices, and suppose that whenever two vertices $a$ and $b$ are symmetrically adjacent
in $\mathit{edges}$ — that is, some edge of $\mathit{edges}$ has endpoints $\{a,b\}$ —
the vertices $a$ and $b$ are connected by a path through $\mathit{edges}'$. Then for any
vertices $u$ and $v$, if $u$ and $v$ are connected by a path through $\mathit{edges}$,
they are also connected by a path through $\mathit{edges}'$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.reach_lift {n : ℕ} {edges edges' : List (WEdge n)}
    (h : ∀ a b, SymAdj edges a b → Reach edges' a b)
    {u v : Fin n} (hr : Reach edges u v) : Reach edges' u v := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih => exact ih.trans (h _ _ hcd)
