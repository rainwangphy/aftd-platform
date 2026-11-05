import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MuStar

/-!
# not_mu_star_nine

Topic: combinatorial_games   Node: 862e822f5463

Provenance: helper lemma. arXiv:2611.05898, Definition 2.1

The natural number 9 does not satisfy mu_star.
-/

/-- The integer 9 does not satisfy mu_star. -/
theorem not_mu_star_nine : ¬ mu_star 9 := by
  intro h
  have hp : Nat.Prime 3 := by norm_num
  have hne : 3 ≠ 2 := by norm_num
  have hdiv : 3^2 ∣ 9 := by norm_num
  exact h 3 hp hne hdiv
