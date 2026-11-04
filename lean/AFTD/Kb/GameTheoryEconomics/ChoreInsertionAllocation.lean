import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreInsertionSlots

/-!
# chore_insertion_allocation

Topic: fair_division   Node: a9030e55c44d

Provenance: formalization of a published result. Source: arXiv:2611.00432, Algorithm 1

Given an implicit number of agents n, an agent sequence σ : ℕ → Fin n, costs c : Fin n → ℕ → ℝ, and m : ℕ, chore_insertion_allocation σ c m : Fin m → Fin n is the allocation assigning each chore d : Fin m to agent σ k, where k < m is the unique slot holding d under chore_insertion_slots σ c m (or 0 if none exists).
-/

/-- The allocation at time m under chore insertion. -/
noncomputable def chore_insertion_allocation {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (m : ℕ) : Fin m → Fin n := fun d => σ (if h : ∃ k < m, chore_insertion_slots σ c m k = d.val then Classical.choose h else 0)
