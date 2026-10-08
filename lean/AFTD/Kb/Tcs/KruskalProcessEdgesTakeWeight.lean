import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFFind
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalProcessEdges
import AFTD.Kb.Tcs.KruskalProcessEdgesAcc
import AFTD.Kb.Tcs.KruskalTotalWeight
import AFTD.Kb.Tcs.KruskalUFFindDef
import AFTD.Kb.Tcs.KruskalTotalWeightNil

/-!
# Kruskal.processEdges_take_weight

Topic: graphs   Node: a2c7fb001d1e

Provenance: helper lemma. TCSlib, `Kruskal.processEdges_take_weight`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Optimality.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weight contributed by an accepted edge. Fix a natural number $n$ and a union-find state $\mathit{uf}$ over $n$ nodes, and let
$e$ be a weighted edge over $n$ vertices — with endpoints $u_e, v_e$ and weight $w_e$ —
followed by a list $\mathit{rest}$ of further weighted edges. Suppose the endpoints of
$e$ lie in different components, that is, $\mathit{uf}(u_e) \ne \mathit{uf}(v_e)$. Then
the total weight of the edge-selection sweep applied to the list $e :: \mathit{rest}$
starting from $\mathit{uf}$ and an empty accumulator equals $w_e$ plus the total weight
of the sweep applied to $\mathit{rest}$ starting from an empty accumulator and the state
obtained by merging the components of $u_e$ and $v_e$ in $\mathit{uf}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.processEdges_take_weight {n : ℕ} {e : WEdge n} {rest : List (WEdge n)} {uf : UF n}
    (h : uf.find e.u ≠ uf.find e.v) :
    totalWeight (processEdges (e :: rest) uf []) =
      e.weight + totalWeight (processEdges rest (uf.merge e.u e.v) []) := by
  rw [show processEdges (e :: rest) uf [] = if uf.find e.u ≠ uf.find e.v then
    processEdges rest (uf.merge e.u e.v) [e] else processEdges rest uf [] from rfl,
    if_pos h, processEdges_acc, List.reverse_singleton]
  rfl
