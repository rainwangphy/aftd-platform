import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUFInit
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalProcessEdges
import AFTD.Kb.Tcs.KruskalUFInitFind

/-!
# Kruskal.kruskal

Topic: graphs   Node: 2c3bfcd66945

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.kruskal`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{kruskal}\,n\,\mathit{edges}$ sorts the edge list by weight and then
runs \texttt{processEdges} on the sorted list starting from the identity
union-find, returning the selected spanning-tree edges.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.kruskal (n : ℕ) (edges : List (WEdge n)) : List (WEdge n) :=
  let sorted := edges.mergeSort (fun e₁ e₂ => decide (e₁.weight ≤ e₂.weight))
  processEdges sorted (UF.init n) []
