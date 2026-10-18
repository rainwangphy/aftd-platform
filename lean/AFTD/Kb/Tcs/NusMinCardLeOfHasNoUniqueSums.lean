import AFTD.Prelude
import AFTD.Kb.Tcs.NusMinCard
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums

/-!
# nus_min_card_le_of_has_no_unique_sums

Topic: combinatorics   Node: a6eb061466a4

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

If A is a subset of Z/pZ with no unique sums, then m(p) ≤ |A|.
-/

/-- If A is a subset of Z/pZ with no unique sums, then m(p) ≤ |A|. -/
theorem nus_min_card_le_of_has_no_unique_sums {p : ℕ} (A : Finset (ZMod p)) (hA : finset_has_no_unique_sums A) : nus_min_card p ≤ A.card := by
  unfold nus_min_card
  apply Nat.sInf_le
  exact ⟨A, hA, rfl⟩
