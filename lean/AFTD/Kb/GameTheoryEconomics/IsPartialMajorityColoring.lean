import AFTD.Prelude

/-!
# is_partial_majority_coloring

Topic: combinatorial_games   Node: 0049e90e8eea

Provenance: formalization of a published result. Source: arXiv:2611.32746: The majority game chromatic number for dense random graphs

A partial colouring of a finite graph G by Boolean colours satisfies the majority condition if every coloured vertex has at most half its neighbours in its own colour.
-/

/-- A partial colouring satisfies the majority condition if every coloured vertex has at most half its neighbours in its own colour. -/
def is_partial_majority_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Option Bool) : Prop := ∀ v col, c v = some col →
    2 * ((G.neighborFinset v).filter (fun w => c w = some col)).card ≤ G.degree v
