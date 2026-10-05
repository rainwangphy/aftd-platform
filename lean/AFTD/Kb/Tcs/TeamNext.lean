import AFTD.Prelude

/-!
# team_next

Topic: algorithms   Node: f8bbb258127b

The cycle successor relation on positions.
-/

/-- The cycle successor relation on positions. -/
def team_next {m : ℕ} (i j : Fin (2 * m + 3)) : Prop :=
  j.val = i.val + 1 ∨ (i.val = 2 * m + 2 ∧ j.val = 0)

instance team_next_decidable {m : ℕ} (i j : Fin (2 * m + 3)) : Decidable (team_next i j) := by
  unfold team_next; infer_instance
