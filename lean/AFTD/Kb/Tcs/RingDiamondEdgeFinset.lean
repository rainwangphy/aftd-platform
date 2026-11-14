import AFTD.Prelude

/-!
# ring_diamond_edge_finset

Topic: combinatorics   Node: f57a163099fb

Provenance: helper lemma. step towards near_minimum_cycle_counting_bound_real_exponent

The edge set of the ring of 20 diamonds on the 60 vertices (i,c) with i < 20 and c < 3: for each i, the ring vertex (i,0) is joined to the midpoints (i,1) and (i,2), and each of those is joined to the next ring vertex (i+1,0). This is 4 edges per block, 80 edges in total.
-/

open Sym2 in
/-- The 80 edges of a ring of 20 diamonds: block i joins the ring vertices (i,0) and (i+1,0) by two internally disjoint 2-paths through the midpoints (i,1) and (i,2). -/
def ring_diamond_edge_finset : Finset (Sym2 (Fin 20 × Fin 3)) := (Finset.univ.image (fun i : Fin 20 => s((i, (0 : Fin 3)), (i, (1 : Fin 3))))) ∪
  (Finset.univ.image (fun i : Fin 20 => s((i, (1 : Fin 3)), (i + 1, (0 : Fin 3))))) ∪
  (Finset.univ.image (fun i : Fin 20 => s((i, (0 : Fin 3)), (i, (2 : Fin 3))))) ∪
  (Finset.univ.image (fun i : Fin 20 => s((i, (2 : Fin 3)), (i + 1, (0 : Fin 3)))))
