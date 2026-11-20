import AFTD.Prelude

/-!
# cycle_demand_twofactor_graph_edges

Topic: graphs   Node: 50c6f1a0d1d2

Provenance: helper lemma. Periodic two-factor local-state construction for the OP-874 campaign.

The base edges formed by the two factor permutations and the matching.
-/

def cycle_demand_twofactor_graph_edges {X : Type*} [Fintype X] [DecidableEq X]
    (sigma p : X ≃ X) : Finset (Sym2 (X × Bool)) := (Finset.univ.image fun x : X => s((x,false),(sigma x,false))) ∪
    (Finset.univ.image fun x : X => s((x,true),(p x,true))) ∪
    (Finset.univ.image fun x : X => s((x,false),(x,true)))
