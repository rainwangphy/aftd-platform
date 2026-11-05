import AFTD.Prelude

/-!
# fano_triple_indicator

Topic: combinatorics   Node: 0c66b5526e4c

Provenance: helper lemma. step towards fano_free_three_uniform_hypergraph_edge_bound

The indicator (as a real number) of the triple {x,y,z} being a hyperedge of H: fano_triple_indicator H x y z = 1 if insert x {y,z} ∈ H, and 0 otherwise.
-/

/-- Indicator of the hyperedge {x, y, z}, as a real number, for the Fano-free counting argument. -/
def fano_triple_indicator {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (x y z : V) : ℝ := if insert x ({y, z} : Finset V) ∈ H then 1 else 0
