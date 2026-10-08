import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.UF.mergeAll

Topic: graphs   Node: d7ae8f49811b

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.UF.mergeAll`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{mergeAll}\,\mathit{uf}\,\mathit{es}$ folds a list of weighted edges
$\mathit{es}$ into the union-find $\mathit{uf}$ by calling \texttt{merge} on
each edge's endpoints in sequence.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.UF.mergeAll {n : ℕ} (uf : UF n) : List (WEdge n) → UF n
  | [] => uf
  | e :: rest => (uf.merge e.u e.v).mergeAll rest
