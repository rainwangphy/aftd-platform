import AFTD.Prelude
import AFTD.Kb.Optimization.AbelSummationByParts

/-!
# greedy_vector_observable_value

Topic: submodular   Node: dbb9d7ff3f5f

Provenance: helper lemma. folklore

For any positive natural number n (0 < n), vector a, permutation π of Fin n, set function C on Finset (Fin n), and vector z summing to 1, if z saturates each upper set S_{k+1} = (Finset.univ.filter (fun j : Fin n => k.val + 1 ≤ (j : ℕ))).map π.toEmbedding for all k : Fin (n - 1), then the inner product ∑ i, a i * z i equals a(π(0)) + ∑ k : Fin (n - 1), (a(π(k+1)) - a(π(k))) * C(S_{k+1}).
-/

/-- Evaluating an observable on a vector that saturates the upper set chain gives the telescoping capacity sum. -/
lemma greedy_vector_observable_value {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (C : Finset (Fin n) → ℝ) (z : Fin n → ℝ)
    (hz_sum : ∑ i, z i = 1)
    (hS : ∀ k : Fin (n - 1),
      ∑ i ∈ (Finset.univ.filter (fun j : Fin n => k.val + 1 ≤ (j : ℕ))).map π.toEmbedding, z i =
        C ((Finset.univ.filter (fun j : Fin n => k.val + 1 ≤ (j : ℕ))).map π.toEmbedding)) :
    ∑ i, a i * z i = a (π ⟨0, hn⟩) + ∑ k : Fin (n - 1),
      (a (π ⟨k.val + 1, by omega⟩) - a (π ⟨k.val, by omega⟩)) *
        C ((Finset.univ.filter (fun j : Fin n => k.val + 1 ≤ (j : ℕ))).map π.toEmbedding) := by
  rw [abel_summation_by_parts hn a π z hz_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hS k]
