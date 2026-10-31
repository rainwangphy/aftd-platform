import AFTD.Prelude

/-!
# op_639_edge_is_four_transversal

Topic: combinatorics   Node: 2385ccb7e341

Provenance: helper lemma. step towards op_639_intersecting_four_uniform_covering_four_card_le_forty_two

In a 4-uniform intersecting family F, every edge e in F has cardinality 4 and intersects every edge e' in F, hence is a size-4 transversal.
-/

/-- In any 4-uniform intersecting hypergraph, every edge e in F is itself a transversal of size 4. -/
theorem op_639_edge_is_four_transversal
    {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (hunif : ∀ e ∈ F, e.card = 4)
    (hinter : (F : Set (Finset V)).Intersecting)
    (e : Finset V) (he : e ∈ F) :
    e.card = 4 ∧ ∀ e' ∈ F, ¬Disjoint e' e := ⟨hunif e he, fun _ he' => hinter he' he⟩
