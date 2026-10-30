import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissible
import AFTD.Kb.Tcs.AdmissibleCardSqAddFiveLe
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# admissible_card_le_nat_sqrt

Topic: combinatorics   Node: 2f4797923d46

Provenance: formalization of a published result. Source: arXiv:2610.34372, Lemma 2.1

If A is a nonempty admissible subset of {1, ..., N}, then the cardinality of A is at most the integer square root of 6 times N.
-/

/-- The cardinality of a nonempty admissible subset of {1, ..., N} is at most sqrt(6N). -/
theorem admissible_card_le_nat_sqrt (N : ℕ) (A : Finset ℕ)
    (hA_sub : A ⊆ Finset.Icc 1 N) (hA_nonempty : A.Nonempty) (hA_adm : IsAdmissible A) :
    A.card ≤ Nat.sqrt (6 * N) := by
  rw [Nat.le_sqrt']
  have h := admissible_card_sq_add_five_le N A hA_sub hA_nonempty hA_adm
  exact_mod_cast le_trans (Int.le_add_of_nonneg_right (by decide)) h
