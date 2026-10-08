import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalTotalWeight

/-!
# Kruskal.totalWeight_nil

Topic: graphs   Node: 411a39783d88

Provenance: helper lemma. TCSlib, `Kruskal.totalWeight_nil`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total weight of the empty edge list. Over any number of vertices $n$, the total weight of the empty list of weighted edges is
$0$; that is, the sum of the weights of no edges is $\sum_{e \in [\,]} e.\mathit{weight}
= 0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
@[simp] lemma Kruskal.totalWeight_nil {n : ℕ} : totalWeight ([] : List (WEdge n)) = 0 := by
  simp [totalWeight]
