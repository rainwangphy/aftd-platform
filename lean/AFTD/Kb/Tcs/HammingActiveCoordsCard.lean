import AFTD.Prelude
import AFTD.Kb.Tcs.HammingActiveCoords
import AFTD.Kb.Tcs.HammingExceptionalCoords
import AFTD.Kb.Tcs.HammingAllDistinctCoords

/-!
# hamming_active_coords_card

Topic: combinatorics   Node: 48f5a4492c47

Provenance: helper lemma. arXiv:2610.32789 "Triangle-Free Sets in Exact-Distance Hamming Graphs", Proposition 2.2

For vectors $x, y, z : \mathrm{Fin}\, n \to \alpha$, the number of active coordinates is the sum of the coordinates where $x$ is exceptional, where $y$ is exceptional, where $z$ is exceptional, and where all three symbols are distinct.
-/

/-- The size of the active support of three vectors is the sum of the three exceptional coordinate counts and the all-distinct coordinate count. -/
theorem hamming_active_coords_card {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) :
    (hamming_active_coords x y z).card =
      (hamming_exceptional_coords x y z).card +
      (hamming_exceptional_coords y x z).card +
      (hamming_exceptional_coords z x y).card +
      (hamming_all_distinct_coords x y z).card := by
  have key : ∀ i : Fin n,
      (if ¬(x i = y i ∧ y i = z i) then (1:ℕ) else 0) =
        (if (y i = z i ∧ x i ≠ y i) then (1:ℕ) else 0) +
        (if (x i = z i ∧ y i ≠ x i) then (1:ℕ) else 0) +
        (if (x i = y i ∧ z i ≠ x i) then (1:ℕ) else 0) +
        (if (x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i) then (1:ℕ) else 0) := by
    intro i
    by_cases h1 : x i = y i <;> by_cases h2 : y i = z i <;> by_cases h3 : x i = z i <;>
      simp_all [eq_comm]
  simp only [hamming_active_coords, hamming_exceptional_coords, hamming_all_distinct_coords]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => key i)
