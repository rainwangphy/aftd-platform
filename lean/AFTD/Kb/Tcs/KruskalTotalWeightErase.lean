import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalTotalWeight
import AFTD.Kb.Tcs.KruskalTotalWeightNil

/-!
# Kruskal.totalWeight_erase

Topic: graphs   Node: 0f5e424924e7

Provenance: helper lemma. TCSlib, `Kruskal.totalWeight_erase`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total weight after removing an edge. Let $\mathit{edges}$ be a list of weighted edges over $n$ vertices, and let $e$ be a
weighted edge occurring in $\mathit{edges}$. Then the total weight of $\mathit{edges}$
equals the weight of $e$ plus the total weight of the list obtained by deleting the
first occurrence of $e$ from $\mathit{edges}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.totalWeight_erase {n : ℕ} (edges : List (WEdge n)) (e : WEdge n)
    (he : e ∈ edges) :
    totalWeight edges = e.weight + totalWeight (edges.erase e) := by
  unfold totalWeight
  simpa using ((List.perm_cons_erase he).map WEdge.weight).sum_eq
