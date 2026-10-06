import AFTD.Prelude

/-!
# temporal_walk_explores_by

Topic: graphs   Node: 97d1c199bed6

Provenance: formalization of a published result. Source: arXiv:2610.06228 (Hiding a Vertex from the Temporal Explorer), Sec. 2 (exploration)

A walk explores the temporal graph by time T if every vertex is visited at some time t ≤ T.
-/

/-- The walk `w` has visited every vertex by time `T`. -/
def temporal_walk_explores_by {n : ℕ} (w : ℕ → Fin n) (T : ℕ) : Prop :=
  ∀ u, ∃ t ≤ T, w t = u
