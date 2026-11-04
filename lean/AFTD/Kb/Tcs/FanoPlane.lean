import AFTD.Prelude

/-!
# fano_plane

Topic: combinatorics   Node: 34c024d56226

Provenance: formalization of a published result. Source: arXiv:2610.01084 Section 2 Example

The Fano plane PG(2,2) is the 3-uniform hypergraph on Fin 7 whose hyperedges are the seven triples {0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, and {2, 4, 5}.
-/

/-- The Fano plane PG(2,2) represented as a 3-uniform hypergraph on 7 vertices. -/
def fano_plane : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}
