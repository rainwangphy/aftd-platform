import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingKendallTau
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# ranking_kendall_tau_self

Topic: fair_division   Node: 3fe975a56ebc

Provenance: helper lemma. Sanity lemma for ranking_kendall_tau.

A ranking is at Kendall tau distance 0 from itself.
-/

theorem ranking_kendall_tau_self {G : Type*} [Fintype G] [DecidableEq G] {m : ℕ} (r : Fin m ≃ G) :
    ranking_kendall_tau r r = 0 := by
  simp only [ranking_kendall_tau, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ h
  exact absurd h.1 (not_lt.mpr h.2.le)
