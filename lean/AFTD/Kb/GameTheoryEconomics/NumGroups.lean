import AFTD.Prelude

/-!
# numGroups

Topic: general_equilibrium   Node: e56e60fa0d78

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_core_logarithmic_lower_bound

The number of player groups when Fin n is split into consecutive pairs {0,1},{2,3},..., i.e. ceil(n/2).
-/

/-- The number of groups in the pairing construction, ceil(n/2). -/
def numGroups (n : ℕ) : ℕ := (n + 1) / 2
