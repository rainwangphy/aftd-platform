import AFTD.Prelude
import AFTD.Kb.Tcs.IsKConnectedSet
import AFTD.Kb.Tcs.MatroidConnectivity
import AFTD.Kb.Tcs.MatroidNotKConnectedOfExactSeparation

/-!
# matroid_not_k_connected_iff_exact_separation

Topic: combinatorics   Node: 93f902eafa28

Provenance: formalization of a published result. Source: arXiv:2610.29979 Lemma 2.6 -- On k-connected Sets in Matroids

Let $M$ be a finite matroid, let $k \ge 3$ be an integer, and let $Z \subseteq E(M)$ be a $(k-1)$-connected set in $M$. Then $Z$ is not $k$-connected in $M$ if and only if there exists a subset $X \subseteq E(M)$ such that $\lambda_M(X) = k - 2$, $|Z \cap X| \ge k - 1$, and $|Z \setminus X| \ge k - 1$.
-/

/-- A (k-1)-connected set Z in a finite matroid M is not k-connected if and only if it exhibits an exact (k-1)-separation. -/
theorem matroid_not_k_connected_iff_exact_separation {α : Type*} (M : Matroid α) [M.Finite] (k : ℕ) (hk : 3 ≤ k) (Z : Set α) (hZ : Z ⊆ M.E) (hZ_prev : IsKConnectedSet M (k - 1) Z) : ¬ IsKConnectedSet M k Z ↔ ∃ X ⊆ M.E, matroid_connectivity M X = k - 2 ∧ k - 1 ≤ (Z ∩ X).ncard ∧ k - 1 ≤ (Z \ X).ncard := by
  have _ := hZ
  constructor
  · intro hnot
    unfold IsKConnectedSet at hnot hZ_prev
    push Not at hnot
    rcases hnot with ⟨X, hXE, hXlt⟩
    have hprev := hZ_prev X hXE
    refine ⟨X, hXE, ?_⟩
    omega
  · rintro ⟨X, hXE, hcon, hZX, hZX'⟩
    exact matroid_not_k_connected_of_exact_separation M k (by omega) Z ⟨X, hXE, hcon, hZX, hZX'⟩
