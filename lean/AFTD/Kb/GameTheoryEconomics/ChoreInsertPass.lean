import AFTD.Prelude

/-!
# chore_insert_pass

Topic: fair_division   Node: 8bb09e454851

Provenance: formalization of a published result. Source: arXiv:2611.00432, Algorithm 1

Given an implicit number of agents n, an agent sequence σ : ℕ → Fin n, costs c : Fin n → ℕ → ℝ, slot count k : ℕ, slot assignment slots : ℕ → ℕ, and buffer chore b : ℕ, chore_insert_pass returns a pair (slots', b') : (ℕ → ℕ) × ℕ: for k = 0 it returns (slots, b); for k + 1 it recursively processes the first k slots, and at slot k owned by σ k, swaps the buffer with the occupant if the buffer is cheaper to σ k with smaller-index tie-breaking, returning the updated slots and displaced chore.
-/

/-- One pass of the chore insertion buffer through existing slots. -/
noncomputable def chore_insert_pass {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) : ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) × ℕ
| 0, slots, b => (slots, b)
| k + 1, slots, b =>
  let (slots', b') := chore_insert_pass σ c k slots b
  let i := σ k
  let o := slots' k
  if c i b' < c i o ∨ (c i b' = c i o ∧ b' < o) then
    (Function.update slots' k b', o)
  else
    (slots', b')
