import AFTD.Prelude
import AFTD.Kb.Tcs.NotInjOnOfExistsNe
import AFTD.Kb.Tcs.PermSecondDerivativeOddExistsWitnesses
import AFTD.Kb.Tcs.PermSecondDerivative

/-!
# perm_second_derivative_odd_not_injOn

Topic: combinatorics   Node: 3cc8093d6f4d

Provenance: formalization of a published result. Source: arXiv:2610.38237 Theorem 2.10 -- Inflection sets of permutations

For any integer $k \ge 1$, the discrete second derivative map on $\mathrm{Sym}_{2k+1} \setminus \{e, e^r\}$ is not injective.
-/

/-- Theorem 2.10 of arXiv:2610.38237: the discrete second derivative on permutations of odd length 2k+1 is not injective outside {e, e^r}. -/
theorem perm_second_derivative_odd_not_injOn (k : ℕ) (hk : 1 ≤ k) :
    ¬ Set.InjOn (perm_second_derivative (n := 2 * k + 1))
      ({1, Fin.revPerm} : Set (Equiv.Perm (Fin (2 * k + 1))))ᶜ := by
  obtain ⟨σ, π, hne, hσ1, hσrev, hπ1, hπrev, hfeq⟩ := perm_second_derivative_odd_exists_witnesses k hk
  apply not_injOn_of_exists_ne (perm_second_derivative (n := 2 * k + 1)) _ σ π
  · simp [hσ1, hσrev]
  · simp [hπ1, hπrev]
  · exact hne
  · exact hfeq
