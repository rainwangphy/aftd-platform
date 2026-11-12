import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelLexProfileLeLimit
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# prioritized_borel_finite_lex_limit_stabilizes

Topic: automata   Node: 7bdab1b32576

Provenance: helper lemma.

A lexicographically nondecreasing sequence of binary profiles with a coordinatewise limit having finite support is eventually equal to that limit.
-/

theorem prioritized_borel_finite_lex_limit_stabilizes (profiles : ℕ → ℕ → Bool) (limit : ℕ → Bool)
    (hmono : Monotone (fun n => toLex (profiles n)))
    (hlim : ∀ k, ∃ N, ∀ n ≥ N, ∀ i < k, profiles n i = limit i)
    (K : ℕ) (hzero : ∀ i ≥ K, limit i = false) :
    ∃ N, ∀ n ≥ N, profiles n = limit := by
  classical
  obtain ⟨N, hN⟩ := hlim K
  refine ⟨N, ?_⟩
  intro n hn
  have hle := prioritized_borel_lex_profile_le_limit profiles limit hmono hlim n
  by_contra hne
  have hne' : toLex (profiles n) ≠ toLex limit := by simpa using hne
  have hlt : toLex (profiles n) < toLex limit := lt_of_le_of_ne hle hne'
  change Pi.Lex (· < ·) (· < ·) (profiles n) limit at hlt
  obtain ⟨i, _, hbit⟩ := hlt
  by_cases hi : i < K
  · have heq := hN n hn i hi
    rw [heq] at hbit
    exact (lt_irrefl _ hbit)
  · have heq := hzero i (by omega)
    rw [heq] at hbit
    exact (not_lt_of_ge (Bool.false_le (profiles n i))) hbit
