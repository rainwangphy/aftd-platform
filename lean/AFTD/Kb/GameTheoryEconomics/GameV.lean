import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CrossPairCount
import AFTD.Kb.GameTheoryEconomics.Ell

/-!
# gameV

Topic: general_equilibrium   Node: 7ecc9058ba5c

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_core_logarithmic_lower_bound

The constructed 2/3-convex cooperative game v_n(S) = (4n+1)·N(S) - ell(S) on players Fin n.
-/

/-- The witness game v_n(S) = (4n+1) N(S) - ell(S) whose non-convex pairs form a matching. -/
noncomputable def gameV (n : ℕ) (S : Finset (Fin n)) : ℝ := (4 * (n : ℝ) + 1) * crossPairCount S - (ell S : ℝ)
