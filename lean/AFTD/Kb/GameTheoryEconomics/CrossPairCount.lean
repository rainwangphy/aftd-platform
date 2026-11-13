import AFTD.Prelude

/-!
# crossPairCount

Topic: general_equilibrium   Node: bf55f043cd2a

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_core_logarithmic_lower_bound

The number, written as a real number, of ordered pairs (a,b) of elements of S whose group indices a.val/2 and b.val/2 differ (equivalently twice the number of unordered cross-group pairs inside S).
-/

/-- Ordered cross-group pair count N(S); the supermodular part of the constructed game. -/
noncomputable def crossPairCount {n : ℕ} (S : Finset (Fin n)) : ℝ := ∑ a : Fin n, ∑ b : Fin n, (if a ∈ S ∧ b ∈ S ∧ a.val / 2 ≠ b.val / 2 then (1 : ℝ) else 0)
