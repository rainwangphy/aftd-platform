import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFFind
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.processEdges

Topic: graphs   Node: 7ca69d49c92e

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.processEdges`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{processEdges}\,\mathit{es}\,\mathit{uf}\,\mathit{acc}$ scans the
edge list $\mathit{es}$ left-to-right: an edge $e$ is added to the
accumulator and its endpoints are merged whenever
$\mathit{uf}.\mathtt{find}\,e.u \ne \mathit{uf}.\mathtt{find}\,e.v$;
otherwise $e$ is skipped.  The reversed accumulator is returned when the
list is exhausted.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.processEdges {n : ℕ} : List (WEdge n) → UF n → List (WEdge n) → List (WEdge n)
  | [], _, acc => acc.reverse
  | e :: rest, uf, acc =>
    if uf.find e.u ≠ uf.find e.v then
      processEdges rest (uf.merge e.u e.v) (e :: acc)
    else
      processEdges rest uf acc
