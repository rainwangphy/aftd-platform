import AFTD.Prelude

/-!
# poset_edge_braid_map

Topic: combinatorics   Node: c633c7983f0d

Provenance: formalization of a published result. Source: arXiv:2611.15540, eq (3.6)

For a partially ordered set P with decidable equality, poset_edge_braid_map is the bipartite braid map on ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2))² that fixes pairs from the same component and, for an edge l = (y, x) with y ≤ x and z in P × ZMod 2, applies the transposition interchanging (y, 0) and (x, 1) to z while swapping components.
-/

/-- The bipartite solution E_P of the braid equation associated to a poset P on L_P ⊔ Z_P. -/
def poset_edge_braid_map {P : Type*} [PartialOrder P] [DecidableEq P]
    (p : ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2)) × ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2))) :
    ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2)) × ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2)) :=
  let t (l : {p : P × P // p.1 ≤ p.2}) (z : P × ZMod 2) : P × ZMod 2 :=
    if z = (l.1.1, 0) then (l.1.2, 1)
    else if z = (l.1.2, 1) then (l.1.1, 0)
    else z
  match p with
  | (.inl l, .inl l') => (.inl l, .inl l')
  | (.inr z, .inr z') => (.inr z, .inr z')
  | (.inl l, .inr z)  => (.inr (t l z), .inl l)
  | (.inr z, .inl l)  => (.inl l, .inr (t l z))
