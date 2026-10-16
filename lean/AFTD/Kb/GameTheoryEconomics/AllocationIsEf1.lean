import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationBundle

/-!
# allocation_is_ef1

Topic: fair_division   Node: 51934fe7dd86

Provenance: formalization of a published result. Source: arXiv:2610.14994 (Best-of-both-worlds fair division via subsidies), Sec. 2 (definition of EF1).

An allocation is envy-free up to one good (EF1) if for all agents i, j, either i does not envy j, or removing some good from j's bundle removes i's envy.
-/

/-- EF1: for all `i j`, `v_i(A_j) ≤ v_i(A_i)` or some `g ∈ A_j` has `v_i(A_j \ {g}) ≤ v_i(A_i)`. -/
def allocation_is_ef1 {N M : Type*} [Fintype M] [DecidableEq N] [DecidableEq M]
    (v : N → Finset M → ℝ) (A : M → N) : Prop :=
  ∀ i j, v i (allocation_bundle A j) ≤ v i (allocation_bundle A i) ∨
    ∃ g ∈ allocation_bundle A j, v i ((allocation_bundle A j).erase g) ≤ v i (allocation_bundle A i)
