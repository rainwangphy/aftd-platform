import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NumGroups
import AFTD.Kb.GameTheoryEconomics.GroupSet

/-!
# ell

Topic: general_equilibrium   Node: 3a04f0a389d2

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_core_logarithmic_lower_bound

The length of the initial run of full groups contained in S: the number of g in range(numGroups n) such that every group h ≤ g is contained in S.
-/

/-- Length of the initial run of groups fully contained in S; the small correction term of the game. -/
noncomputable def ell {n : ℕ} (S : Finset (Fin n)) : ℕ := by
  classical
  exact ((Finset.range (numGroups n)).filter
    (fun g => ∀ h ∈ Finset.range (g + 1), groupSet h ⊆ S)).card
