import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge

/-!
# Kruskal.totalWeight

Topic: graphs   Node: c1b750b0580e

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.totalWeight`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The total weight of an edge list is the sum of the weights of all its edges:
$\mathtt{totalWeight}\,\mathit{edges} = \sum_{e \in \mathit{edges}} e.\mathit{weight}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.totalWeight {n : ℕ} (edges : List (WEdge n)) : ℕ := (edges.map WEdge.weight).sum
