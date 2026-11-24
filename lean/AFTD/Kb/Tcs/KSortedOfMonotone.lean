import AFTD.Prelude
import AFTD.Kb.Tcs.KSorted
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# k_sorted_of_monotone

Topic: algorithms   Node: b8e3197afde3

Provenance: helper lemma. folklore

If an array $A : \text{Fin } n \to \alpha$ is monotone non-decreasing, then it is $k$-sorted for every $k$.
-/

/-- A monotone array is k-sorted for any k. -/
theorem k_sorted_of_monotone {n : ℕ} (k : ℕ) {α : Type*} [Preorder α] (A : Fin n → α) (hA : Monotone A) : k_sorted k A := by
  intro i hi
  apply hA
  rw [Fin.le_def]
  simp
