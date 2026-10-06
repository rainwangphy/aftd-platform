import AFTD.Prelude

/-!
# is_temporal_walk

Topic: graphs   Node: 852721bc4217

Provenance: formalization of a published result. Source: arXiv:2610.06228 (Hiding a Vertex from the Temporal Explorer), Sec. 2 (temporal walks)

A temporal walk in a temporal graph (G_t)_t: at every time step t the agent either waits or traverses one edge of the snapshot G_t.
-/

/-- A walk of an agent in the temporal graph `G` (snapshot `G t` at time step `t`): at each step it waits or moves along one edge of the current snapshot. -/
def is_temporal_walk {n : ℕ} (G : ℕ → SimpleGraph (Fin n)) (w : ℕ → Fin n) : Prop :=
  ∀ t, w (t + 1) = w t ∨ (G t).Adj (w t) (w (t + 1))
