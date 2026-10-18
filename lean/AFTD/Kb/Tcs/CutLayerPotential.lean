import AFTD.Prelude

/-!
# cut_layer_potential

Topic: graphs   Node: d026edce6a19

Provenance: helper lemma. step towards exists_dist_three_cut_potential_witness

The 4-layer potential takes value 0 on vertices of X with no neighbors in Xᶜ, 1 on vertices of X with a neighbor in Xᶜ, 2 on vertices of Xᶜ with a neighbor in X, and 3 on vertices of Xᶜ with no neighbors in X.
-/

/-- The canonical 4-layer potential for a cut (X, Xᶜ): 0 on the interior of X, 1 on the boundary of X, 2 on the boundary of Xᶜ, and 3 on the interior of Xᶜ. -/
def cut_layer_potential {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : V → ℝ := fun v =>
  if v ∈ X then (if ∃ w ∈ (Xᶜ : Finset V), G.Adj v w then 1 else 0)
  else (if ∃ u ∈ X, G.Adj v u then 2 else 3)
