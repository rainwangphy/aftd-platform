import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationBundle

/-!
# allocation_is_envy_freeable

Topic: fair_division   Node: 4f8edeafc083

Provenance: formalization of a published result. Source: arXiv:2610.14994 (Best-of-both-worlds fair division via subsidies), Sec. 2 (definition of envy-freeability by subsidies).

An allocation is envy-freeable if there are nonnegative payments p such that every agent i weakly prefers its own bundle plus payment to every other bundle plus that agent's payment: v_i(A_i) + p_i ≥ v_i(A_j) + p_j.
-/

/-- Envy-freeable: some nonnegative subsidy vector makes the bundle–payment pairs envy-free. -/
def allocation_is_envy_freeable {N M : Type*} [Fintype M] [DecidableEq N]
    (v : N → Finset M → ℝ) (A : M → N) : Prop :=
  ∃ p : N → ℝ, (∀ i, 0 ≤ p i) ∧
    ∀ i j, v i (allocation_bundle A j) + p j ≤ v i (allocation_bundle A i) + p i
