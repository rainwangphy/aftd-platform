import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationIsEf1
import AFTD.Kb.GameTheoryEconomics.AllocationBundle

/-!
# allocation_is_ef1_of_envy_free

Topic: fair_division   Node: 5c069a516511

Provenance: helper lemma. Sanity lemma for EF1, arXiv:2610.14994 (Best-of-both-worlds fair division via subsidies), Sec. 2.

An envy-free allocation is EF1.
-/

theorem allocation_is_ef1_of_envy_free {N M : Type*} [Fintype M] [DecidableEq N] [DecidableEq M]
    (v : N → Finset M → ℝ) (A : M → N)
    (h : ∀ i j, v i (allocation_bundle A j) ≤ v i (allocation_bundle A i)) :
    allocation_is_ef1 v A :=
  fun i j => Or.inl (h i j)
