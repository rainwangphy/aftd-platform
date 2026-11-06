import AFTD.Prelude
import AFTD.Kb.Tcs.IsPerfectSet

/-!
# is_perfect_set_two

Topic: combinatorics   Node: 4e938c565fa2

Provenance: formalization of a published result. Source: folklore

The singleton set containing the transposition swap 0 1 on Fin 2 is a perfect set of order 2.
-/

/-- The swap on Fin 2 forms a perfect set of order 2. -/
theorem is_perfect_set_two :
    is_perfect_set 2 {Equiv.swap (0 : Fin 2) (1 : Fin 2)} := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro σ hσ
    simp only [Finset.mem_singleton] at hσ
    subst hσ
    dsimp [derangements]
    intro x
    fin_cases x <;> decide
  · intro σ hσ τ hτ hne
    simp only [Finset.mem_singleton] at hσ hτ
    subst hσ hτ
    exact (hne rfl).elim
