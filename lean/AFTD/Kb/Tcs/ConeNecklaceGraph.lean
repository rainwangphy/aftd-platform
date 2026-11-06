import AFTD.Prelude

/-!
# cone_necklace_graph

Topic: graphs   Node: da7bd0adfba6

Provenance: original. Related work: Explicit graph construction for simple_graph_stable_min_two_triangles_odd_conflict_cycle_family; see experiments 16959–16961 and 17491.

For each natural m, the simple graph on vertices 0 through 2m has apex 2m adjacent to every other vertex. For each i from 0 to m−1, it also has a base triangle on cycle vertex i, cycle vertex (i+1) mod m, and private vertex m+i. There are no other edges and no loops.
-/

open Sym2 in
def cone_necklace_graph (m : ℕ) : SimpleGraph (Fin (2 * m + 1)) :=
  let apex : Fin (2 * m + 1) := ⟨2 * m, by omega⟩
  let cycle : Fin m → Fin (2 * m + 1) := fun i => ⟨i.val, by omega⟩
  let privateVertex : Fin m → Fin (2 * m + 1) := fun i => ⟨m + i.val, by omega⟩
  let next : Fin m → Fin m := fun i =>
    ⟨(i.val + 1) % m, Nat.mod_lt _ (by have := i.isLt; omega)⟩
  SimpleGraph.fromEdgeSet {e |
    (∃ v : Fin (2 * m + 1), v ≠ apex ∧ e = s(apex, v)) ∨
    ∃ i : Fin m,
      e = s(cycle i, cycle (next i)) ∨
      e = s(cycle i, privateVertex i) ∨
      e = s(cycle (next i), privateVertex i)}
