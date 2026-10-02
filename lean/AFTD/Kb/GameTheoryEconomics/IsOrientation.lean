import AFTD.Prelude

/-!
# is_orientation

Topic: fair_division   Node: 314cfbcdae09

An allocation of the edges of a multigraph is an orientation if every edge goes to one of its two endpoints.
-/

/-- The allocation `σ` is an orientation of the multigraph whose edge `e` joins `(ends e).1` and `(ends e).2`: every edge goes to one of its two endpoints. -/
def is_orientation {m n : ℕ} (ends : Fin m → Fin n × Fin n) (σ : Fin m → Fin n) : Prop :=
  ∀ e, σ e = (ends e).1 ∨ σ e = (ends e).2
