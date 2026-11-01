import AFTD.Prelude

/-!
# majority_three

Topic: information   Node: 6893835612a2

Provenance: formalization of a published result. Source: folklore

The majority function majority_three : (Fin 3 → Bool) → ℝ maps each x : Fin 3 → Bool to ℝ by returning -1 if ((if x 0 then 1 else 0) + (if x 1 then 1 else 0) + (if x 2 then 1 else 0) : ℕ) ≥ 2, and 1 otherwise.
-/

/-- The 3-bit majority function on Fin 3 -> Bool with values in {-1, 1}. -/
def majority_three : (Fin 3 → Bool) → ℝ := fun x ↦ if ((if x 0 then 1 else 0) + (if x 1 then 1 else 0) + (if x 2 then 1 else 0) : ℕ) ≥ 2 then -1 else 1
