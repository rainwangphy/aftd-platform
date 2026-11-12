import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# prioritized_borel_lex_profile_le_limit

Topic: automata   Node: a88d46cb99bf

Provenance: helper lemma. arXiv:2611.10136, Section 5.2.2; lexicographic priority profiles

Each member of a lexicographically nondecreasing binary profile sequence is at most its coordinatewise limit.
-/

theorem prioritized_borel_lex_profile_le_limit (profiles : ℕ → ℕ → Bool) (limit : ℕ → Bool)
    (hmono : Monotone (fun n => toLex (profiles n)))
    (hlim : ∀ k, ∃ N, ∀ n ≥ N, ∀ i < k, profiles n i = limit i) :
    ∀ n, toLex (profiles n) ≤ toLex limit := by
  classical
  intro n
  apply le_of_not_gt
  intro hgt
  change Pi.Lex (· < ·) (· < ·) limit (profiles n) at hgt
  obtain ⟨i, hprev, hbit⟩ := hgt
  obtain ⟨N, hN⟩ := hlim (i+1)
  let j := max n N
  have hcmp := hmono (show n ≤ j from le_max_left _ _)
  have hlt : toLex (profiles j) < toLex (profiles n) := by
    change Pi.Lex (· < ·) (· < ·) (profiles j) (profiles n)
    refine ⟨i, ?_, ?_⟩
    · intro k hk
      rw [hN j (le_max_right _ _) k (by omega)]
      exact hprev k hk
    · rw [hN j (le_max_right _ _) i (by omega)]
      exact hbit
  exact (not_lt_of_ge hcmp) hlt
