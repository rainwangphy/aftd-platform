import AFTD.Prelude
import AFTD.Kb.Tcs.NusMinCard
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsSumsetOfBalanced
import AFTD.Kb.Tcs.NusMinCardLeOfHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums

/-!
# nus_min_card_le_sq_of_midpoint_balanced

Topic: combinatorics   Node: ab121148f748

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

If B is a midpoint-balanced subset of Z/pZ, then m(p) ≤ |B|².
-/

/-- If B is a midpoint-balanced subset of Z/pZ, then m(p) ≤ |B|². -/
theorem nus_min_card_le_sq_of_midpoint_balanced {p : ℕ} (B : Finset (ZMod p)) (hB : finset_is_midpoint_balanced B) : nus_min_card p ≤ B.card ^ 2 := by
  have h_nus := finset_has_no_unique_sums_sumset_of_balanced B hB
  have h_le := nus_min_card_le_of_has_no_unique_sums ((B ×ˢ B).image (fun x => x.1 + x.2)) h_nus
  have h_card : ((B ×ˢ B).image (fun x => x.1 + x.2)).card ≤ B.card ^ 2 := by
    calc
      ((B ×ˢ B).image (fun x => x.1 + x.2)).card ≤ (B ×ˢ B).card := Finset.card_image_le
      _ = B.card ^ 2 := by rw [Finset.card_product, sq]
  omega
