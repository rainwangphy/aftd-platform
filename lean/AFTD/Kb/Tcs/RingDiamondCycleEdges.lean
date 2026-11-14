import AFTD.Prelude

/-!
# ring_diamond_cycle_edges

Topic: combinatorics   Node: 051524936432

Provenance: helper lemma. step towards near_minimum_cycle_counting_bound_real_exponent

For a set S of blocks, the edge set of the cycle that goes once around the ring, using for block i the route through the midpoint (i,2) (two edges) when i ∈ S and the route through (i,1) when i ∉ S; this set has 2 edges per block, 40 in total.
-/

open Sym2 in
/-- The 40-edge set of the ring cycle that uses the upper route through (i,2) for the blocks i in S and the lower route through (i,1) for the other blocks. -/
def ring_diamond_cycle_edges (S : Finset (Fin 20)) : Finset (Sym2 (Fin 20 × Fin 3)) := (Finset.univ.image (fun i : Fin 20 =>
      if i ∈ S then s((i, (0 : Fin 3)), (i, (2 : Fin 3)))
      else s((i, (0 : Fin 3)), (i, (1 : Fin 3))))) ∪
  (Finset.univ.image (fun i : Fin 20 =>
      if i ∈ S then s((i, (2 : Fin 3)), (i + 1, (0 : Fin 3)))
      else s((i, (1 : Fin 3)), (i + 1, (0 : Fin 3)))))
