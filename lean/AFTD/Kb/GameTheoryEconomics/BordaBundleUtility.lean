import AFTD.Prelude

/-!
# borda_bundle_utility

Topic: fair_division   Node: 7799051c0df6

Provenance: formalization of a published result. Source: A Social Welfare Optimal Sequential Allocation Procedure

For a strict ranking r of m goods (where r 0 is the top-ranked good), the additive Borda utility of a bundle of goods S assigns m - rank(g) points to each good g in S, so the top good has utility m and the worst good has utility 1.
-/

/-- Additive Borda utility of a bundle of goods under a strict ranking of m goods. -/
def borda_bundle_utility (m : ℕ) (r : Fin m ≃ Fin m) (S : Finset (Fin m)) : ℕ :=
  ∑ g ∈ S, (m - (r.symm g : ℕ))
