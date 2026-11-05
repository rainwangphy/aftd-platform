import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MuStar
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mu_star_one

Topic: combinatorial_games   Node: bc759aed8948

Provenance: helper lemma. arXiv:2611.05898, Definition 2.1

The natural number 1 satisfies mu_star.
-/

/-- The integer 1 satisfies mu_star. -/
theorem mu_star_one : mu_star 1 := by
  intro p hp _ hdiv
  have hle : p ^ 2 ≤ 1 := Nat.le_of_dvd Nat.one_pos hdiv
  have h2 : 2 ≤ p := hp.two_le
  nlinarith
