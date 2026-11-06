import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EpsteinRemotenessTwentyNine
import AFTD.Kb.GameTheoryEconomics.EpsteinRemoteness

/-!
# epstein_remoteness_four_nonempty

Topic: combinatorial_games   Node: d7a35d6a90aa

Provenance: helper lemma. arXiv:2611.05898 Ex 1.4

There exists a natural number n such that epstein_remoteness n = 4.
-/

/-- There exists at least one position with remoteness 4 in Epstein's game. -/
theorem epstein_remoteness_four_nonempty : ∃ n : ℕ, epstein_remoteness n = 4 := ⟨29, epstein_remoteness_twenty_nine⟩
