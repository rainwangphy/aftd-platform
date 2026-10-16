import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationIsEnvyFreeable
import AFTD.Kb.GameTheoryEconomics.AllocationBundle

/-!
# allocation_is_envy_freeable_of_envy_free

Topic: fair_division   Node: 88545fdb4748

Provenance: helper lemma. Sanity lemma for envy-freeability, arXiv:2610.14994 (Best-of-both-worlds fair division via subsidies), Sec. 2.

An envy-free allocation is envy-freeable (with zero payments).
-/

theorem allocation_is_envy_freeable_of_envy_free {N M : Type*} [Fintype M] [DecidableEq N]
    (v : N → Finset M → ℝ) (A : M → N)
    (h : ∀ i j, v i (allocation_bundle A j) ≤ v i (allocation_bundle A i)) :
    allocation_is_envy_freeable v A :=
  ⟨fun _ => 0, fun _ => le_rfl, fun i j => by simpa using h i j⟩
