import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelLexProfileLeLimit
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# prioritized_borel_lex_strict_changes_infinite_limit

Topic: automata   Node: d17655c045aa

Provenance: helper lemma. arXiv:2611.10136, Section 5.2.2; lexicographic priority profiles

If a lexicographically nondecreasing sequence of binary profiles has strict increases arbitrarily late, its coordinatewise limit contains true entries arbitrarily late.
-/

theorem prioritized_borel_lex_strict_changes_infinite_limit (profiles : ℕ → ℕ → Bool)
    (limit : ℕ → Bool)
    (hmono : Monotone (fun n => toLex (profiles n)))
    (hlim : ∀ k, ∃ N, ∀ n ≥ N, ∀ i < k, profiles n i = limit i)
    (hstrict : ∀ N, ∃ n ≥ N, toLex (profiles n) < toLex (profiles (n+1))) :
    ∀ K, ∃ i ≥ K, limit i = true := by
  classical
  intro K
  by_contra h
  push_neg at h
  have hzero : ∀ i ≥ K, limit i = false := by
    intro i hi
    have := h i hi
    cases hbit : limit i <;> simp_all
  obtain ⟨N, hN⟩ := hlim K
  have heq : ∀ n ≥ N, profiles n = limit := by
    intro n hn
    have hle := prioritized_borel_lex_profile_le_limit profiles limit hmono hlim n
    by_contra hne
    have hne' : toLex (profiles n) ≠ toLex limit := by simpa using hne
    have hlt : toLex (profiles n) < toLex limit := lt_of_le_of_ne hle hne'
    change Pi.Lex (· < ·) (· < ·) (profiles n) limit at hlt
    obtain ⟨i, _, hbit⟩ := hlt
    by_cases hi : i < K
    · have hh := hN n hn i hi
      rw [hh] at hbit
      exact (lt_irrefl _ hbit)
    · have hh := hzero i (by omega)
      rw [hh] at hbit
      exact (not_lt_of_ge (Bool.false_le (profiles n i))) hbit
  obtain ⟨n, hn, hlt⟩ := hstrict N
  rw [heq n hn, heq (n+1) (by omega)] at hlt
  exact (lt_irrefl _ hlt)
