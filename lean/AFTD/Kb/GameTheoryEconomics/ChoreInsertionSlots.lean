import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreInsertPass

/-!
# chore_insertion_slots

Topic: fair_division   Node: bb188c69c888

Provenance: formalization of a published result. Source: arXiv:2611.00432, Algorithm 1

Given an implicit number of agents n, an agent sequence σ : ℕ → Fin n, and costs c : Fin n → ℕ → ℝ, chore_insertion_slots m : ℕ → ℕ returns the slot assignment of chores after m arrivals in chore insertion: at m = 0 it is id, and at m + 1 it passes the new chore m through the previous m slots using chore_insert_pass and places the remaining buffer chore in slot m.
-/

/-- The slot contents after m chore arrivals under chore insertion. -/
noncomputable def chore_insertion_slots {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) : ℕ → (ℕ → ℕ)
| 0 => id
| m + 1 =>
  let prev := chore_insertion_slots σ c m
  let (new_slots, b) := chore_insert_pass σ c m prev m
  Function.update new_slots m b
