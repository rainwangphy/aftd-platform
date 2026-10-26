import AFTD.Prelude
import AFTD.Kb.Tcs.Zmod8CubeGraph

/-!
# zmod8_cube_graph_decidable_adj

Topic: combinatorics   Node: 10e121eb2be2

Provenance: helper lemma. step towards not_all_sharp_cyclic_graphs_circulant_at_powers_of_two

Adjacency in the cube graph on ZMod 8 is decidable, since it reduces to deciding the residue of x + y.
-/

/-- Decidability of adjacency in the cube graph on ZMod 8, from decidability of the residue value. -/
instance zmod8_cube_graph_decidable_adj : DecidableRel zmod8_cube_graph.Adj := fun x y => by
  change Decidable ((x + y).val = 1 ∨ (x + y).val = 3 ∨ (x + y).val = 5)
  infer_instance
