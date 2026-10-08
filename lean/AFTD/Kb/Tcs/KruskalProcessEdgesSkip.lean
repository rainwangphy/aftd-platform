import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFFind
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalProcessEdges
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.processEdges_skip

Topic: graphs   Node: 81abf474fd63

Provenance: helper lemma. TCSlib, `Kruskal.processEdges_skip`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Optimality.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Skipping an intra-component edge in the sweep. Fix a number of nodes $n$, a union-find state $\mathit{uf} : \mathrm{Fin}\,n \to \bbn$,
a weighted edge $e$ over $n$ vertices with endpoints $u$ and $v$, and a list
$\mathit{rest}$ of further weighted edges over $n$ vertices. Suppose the two endpoints
of $e$ already have the same representative in $\mathit{uf}$, that is, $\mathit{uf}(u) =
\mathit{uf}(v)$. Then the edge-selection sweep applied to the list $e :: \mathit{rest}$
starting from state $\mathit{uf}$ with empty accumulator returns exactly the same edge
list as the sweep applied to $\mathit{rest}$ starting from the same state $\mathit{uf}$
with empty accumulator.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.processEdges_skip {n : ℕ} {e : WEdge n} {rest : List (WEdge n)} {uf : UF n}
    (h : uf.find e.u = uf.find e.v) :
    processEdges (e :: rest) uf [] = processEdges rest uf [] := if_neg (by aesop)
