import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# prioritized_borel_lex_restrict_monotone

Topic: automata   Node: 987fab9be515

Provenance: helper lemma. arXiv:2611.10136, Section 5.2.2; lexicographic priority profiles

Restricting lexicographically ordered infinite binary profiles to any fixed finite prefix preserves their order.
-/

theorem prioritized_borel_lex_restrict_monotone (k : ℕ) (p q : ℕ → Bool)
    (hpq : toLex p ≤ toLex q) :
    toLex (fun i : Fin k => p i) ≤ toLex (fun i : Fin k => q i) := by
  classical
  apply le_of_not_gt
  intro hgt
  change Pi.Lex (· < ·) (· < ·) (fun i : Fin k => q i) (fun i : Fin k => p i) at hgt
  obtain ⟨i, hprev, hbit⟩ := hgt
  have hfull : toLex q < toLex p := by
    change Pi.Lex (· < ·) (· < ·) q p
    refine ⟨i.val, ?_, hbit⟩
    intro j hj
    have hjk : j < k := lt_trans hj i.isLt
    simpa using hprev ⟨j, hjk⟩ hj
  exact (not_lt_of_ge hpq) hfull
