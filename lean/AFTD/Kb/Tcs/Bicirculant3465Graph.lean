import AFTD.Prelude

/-!
# bicirculant_3465_graph

Topic: graphs   Node: 5dc2818ccd6d

Provenance: helper lemma. step towards op_1151_bicirculant_3465_is_hamiltonian

The bicirculant graph B(3465; {2310,-2310}, {0,35,77,275}, {1155,-1155}) of order 6930 on vertex set Fin 2 × ZMod 3465, named so the cycle-witness lemmas and the target can refer to it.
-/

def bicirculant_3465_graph : SimpleGraph (Fin 2 × ZMod 3465) := SimpleGraph.fromRel fun (u v : Fin 2 × ZMod 3465) =>
    (u.1 = 0 ∧ v.1 = 0 ∧ v.2 - u.2 ∈ ({2310, -2310} : Finset (ZMod 3465))) ∨
    (u.1 = 1 ∧ v.1 = 1 ∧ v.2 - u.2 ∈ ({1155, -1155} : Finset (ZMod 3465))) ∨
    (u.1 = 0 ∧ v.1 = 1 ∧ v.2 - u.2 ∈ ({0, 35, 77, 275} : Finset (ZMod 3465)))
