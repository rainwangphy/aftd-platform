import AFTD.Prelude
import AFTD.Kb.Tcs.IsKConnectedSet
import AFTD.Kb.Tcs.MatroidConnectivity

/-!
# matroid_not_k_connected_of_exact_separation

Topic: combinatorics   Node: edb4787c930d

Provenance: formalization of a published result. Source: arXiv:2610.29979, Lemma 2.6

Let $M$ be a matroid, let $k \ge 2$ be an integer, and let $Z$ be a set in $M$. If there exists a subset $X \subseteq E(M)$ such that $\lambda_M(X) = k - 2$, $|Z \cap X| \ge k - 1$, and $|Z \setminus X| \ge k - 1$, then $Z$ is not $k$-connected in $M$.
-/

/-- If Z exhibits an exact (k-1)-separation of M, then Z is not k-connected in M. -/
theorem matroid_not_k_connected_of_exact_separation {α : Type*} (M : Matroid α) (k : ℕ) (hk : 2 ≤ k) (Z : Set α) (hX : ∃ X ⊆ M.E, matroid_connectivity M X = k - 2 ∧ k - 1 ≤ (Z ∩ X).ncard ∧ k - 1 ≤ (Z \ X).ncard) : ¬ IsKConnectedSet M k Z := by
  intro hconn
  rcases hX with ⟨X, hXE, hcon, hZX, hZ_not_X⟩
  have hle := hconn X hXE
  rw [hcon] at hle
  have hmin : k - 1 ≤ min (min (Z ∩ X).ncard (Z \ X).ncard) (k - 1) := by
    apply le_min
    · apply le_min
      · exact hZX
      · exact hZ_not_X
    · exact le_rfl
  have hcontra := hmin.trans hle
  omega
