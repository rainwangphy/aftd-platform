import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicPermutationSubtractionSet

/-!
# cyclic_permutation_subtraction_set_ne_nil

Topic: combinatorial_games   Node: bc0c25aea03f

Provenance: helper lemma. arXiv:2611.09157

For natural numbers d, s, a, b with 1 ≤ d, 1 ≤ a, and 1 ≤ b, every word w in the finite set cyclic_permutation_subtraction_set d s a b is nonempty (w ≠ []).
-/

/-- Words in the cyclic permutation subtraction set are nonempty when d >= 1 and a, b >= 1. -/
theorem cyclic_permutation_subtraction_set_ne_nil (d s a b : ℕ)
    (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∀ w ∈ cyclic_permutation_subtraction_set d s a b, w ≠ [] := by
  intro w hw
  simp only [cyclic_permutation_subtraction_set, Finset.mem_insert, Finset.mem_singleton] at hw
  intro h
  rcases hw with rfl | rfl
  · have hlen : ((List.replicate a (List.finRange d)).flatten).length = a * d := by
      simp [List.length_flatten]
    have hz : ((List.replicate a (List.finRange d)).flatten).length = 0 := by
      rw [h, List.length_nil]
    rw [hz] at hlen
    have : 1 ≤ a * d := Nat.mul_le_mul ha hd
    omega
  · have hlen : ((List.replicate b ((List.finRange d).rotate s)).flatten).length = b * d := by
      simp [List.length_flatten]
    have hz : ((List.replicate b ((List.finRange d).rotate s)).flatten).length = 0 := by
      rw [h, List.length_nil]
    rw [hz] at hlen
    have : 1 ≤ b * d := Nat.mul_le_mul hb hd
    omega
