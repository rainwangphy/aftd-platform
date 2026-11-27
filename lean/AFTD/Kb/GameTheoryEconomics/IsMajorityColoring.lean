import AFTD.Prelude

/-!
# is_majority_coloring

Topic: combinatorial_games   Node: dd6d4d6d19af

Provenance: formalization of a published result. Source: arXiv:2611.32746 Sec 1, arXiv:2609.37796 Sec 1

A partial 2-colouring of a graph satisfies the majority condition if every coloured vertex has at most half its neighbours of the same colour.
-/

/-- A partial 2-colouring satisfies the majority condition if every coloured vertex has at most half its neighbours of the same colour. -/
def is_majority_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Option Bool) : Prop :=
  ∀ v b, c v = some b →
    ((G.neighborFinset v).filter (fun u => c u = some b)).card ≤ G.degree v / 2
