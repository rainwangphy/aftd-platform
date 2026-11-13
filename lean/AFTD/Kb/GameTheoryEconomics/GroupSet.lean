import AFTD.Prelude

/-!
# groupSet

Topic: general_equilibrium   Node: 57653f379be4

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_core_logarithmic_lower_bound

The g-th group of players, i.e. the players i : Fin n with i.val / 2 = g (so {0,1},{2,3},... and a final singleton when n is odd).
-/

/-- The g-th pair-group of players, {2g, 2g+1} intersected with Fin n. -/
def groupSet {n : ℕ} (g : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val / 2 = g)
