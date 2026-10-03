import AFTD.Prelude

/-!
# has_out_degree_two_orientation

Topic: fair_division   Node: 9324c1edb824

The simple graph underlying the multigraph has an orientation in which every vertex has out-degree at most two.
-/

/-- The simple graph underlying the multigraph `ends` has an orientation in which every vertex has out-degree at most two: a relation `T` (`T i j` meaning the arc `i → j`) covering every edge in at least one direction, with at most two out-neighbours per vertex. -/
def has_out_degree_two_orientation {m n : ℕ} (ends : Fin m → Fin n × Fin n) : Prop :=
  ∃ T : Fin n → Fin n → Bool,
    (∀ e, T (ends e).1 (ends e).2 = true ∨ T (ends e).2 (ends e).1 = true) ∧
    ∀ i, (Finset.univ.filter fun j => T i j = true).card ≤ 2
