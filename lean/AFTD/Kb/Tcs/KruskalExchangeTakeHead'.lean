import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalExchangeTakeHead
import AFTD.Kb.Tcs.KruskalSymAdj
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReachLift
import AFTD.Kb.Tcs.KruskalReach

/-!
# Kruskal.exchange_take_head'

Topic: graphs   Node: e4c3b94dca1a

Provenance: helper lemma. TCSlib, `Kruskal.exchange_take_head'`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Exchange.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Edge exchange preserving reachability, reversed orientation. Fix $n$ and consider weighted edges on a vertex set of size $n$, each edge carrying a
first and a second endpoint. For a list of edges $L$, write $a \leadsto_L b$ to mean
that $a$ reaches $b$ through $L$, i.e.\ $a$ and $b$ are joined by a path whose edges lie
in $L$ (the reflexive–transitive closure of the symmetric adjacency relation induced by
$L$). Let $\mathit{base}$ and $\mathit{rest}$ be lists of weighted edges, and let $g$
and $e$ be weighted edges, with first and second endpoints $g_1, g_2$ and $e_1, e_2$
respectively. Suppose that, using the edges in the concatenation $\mathit{base}
\mathbin{+\!\!+} \mathit{rest}$, the endpoint $e_1$ reaches $g_2$ and the endpoint $g_1$
reaches $e_2$. Then for every pair of vertices $a, b$: if $a \leadsto b$ using the list
obtained by placing $g$ at the front of $\mathit{rest}$ and appending that to
$\mathit{base}$, then $a \leadsto b$ using $\mathit{base} \mathbin{+\!\!+} \mathit{rest}
\mathbin{+\!\!+} [e]$, the concatenation of $\mathit{base}$, $\mathit{rest}$, and the
single edge $e$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.exchange_take_head' {n : ℕ} {base rest : List (WEdge n)} {g e : WEdge n}
    (h1 : Reach (base ++ rest) e.u g.v) (h2 : Reach (base ++ rest) g.u e.v) :
    ∀ a b, Reach (base ++ g :: rest) a b → Reach (base ++ rest ++ [e]) a b := by
  intro a b hab
  refine exchange_take_head (g := ⟨g.v, g.u, g.weight⟩) h1 h2 a b ?_
  apply reach_lift (edges := base ++ g :: rest) _ hab
  intro x y hxy
  exact Relation.ReflTransGen.single (by unfold SymAdj at *; aesop)
