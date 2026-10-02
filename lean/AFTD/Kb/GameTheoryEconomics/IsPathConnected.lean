import AFTD.Prelude

/-!
# is_path_connected

Topic: fair_division   Node: e11452c68565

A set of items on the path 0, 1, ..., m-1 is connected if it contains every item between two of its items.
-/

/-- A set of items on a path `0, 1, …, m - 1` is connected: it contains every item lying between two of its items. -/
def is_path_connected {m : ℕ} (B : Finset (Fin m)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ z, x ≤ z → z ≤ y → z ∈ B
