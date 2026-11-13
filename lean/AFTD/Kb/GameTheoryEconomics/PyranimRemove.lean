import AFTD.Prelude

/-!
# pyranim_remove

Topic: combinatorial_games   Node: eff34b3eca49

Provenance: formalization of a published result. Source: arXiv:2611.16153 Sec. 1.1

The position resulting from removing chip c = (i, j) from X, which removes c and all chips (a, b) in X that contain (i, j) (satisfying a ≤ i and j ≤ b).
-/

/-- The position resulting from removing chip c and all chips containing it. -/
def pyranim_remove (X : Finset (ℕ × ℕ)) (c : ℕ × ℕ) : Finset (ℕ × ℕ) := X.filter (fun ⟨a, b⟩ => ¬ (a ≤ c.1 ∧ c.2 ≤ b))
